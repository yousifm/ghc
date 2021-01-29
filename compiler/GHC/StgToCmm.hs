{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE BangPatterns #-}

-----------------------------------------------------------------------------
--
-- Stg to C-- code generation
--
-- (c) The University of Glasgow 2004-2006
--
-----------------------------------------------------------------------------

module GHC.StgToCmm ( codeGen ) where

#include "HsVersions.h"

import GHC.Prelude as Prelude

import GHC.Driver.Backend
import GHC.Driver.Session

import GHC.StgToCmm.Prof (initInfoTableProv, initCostCentres, ldvEnter)
import GHC.StgToCmm.Monad
import GHC.StgToCmm.Env
import GHC.StgToCmm.Bind
import GHC.StgToCmm.DataCon
import GHC.StgToCmm.Layout
import GHC.StgToCmm.Utils
import GHC.StgToCmm.Closure
import GHC.StgToCmm.Hpc
import GHC.StgToCmm.Ticky
import GHC.StgToCmm.Types (ModuleLFInfos)

import GHC.Cmm
import GHC.Cmm.Utils
import GHC.Cmm.CLabel
import GHC.Cmm.Graph

import GHC.Stg.Syntax

import GHC.Types.CostCentre
import GHC.Types.IPE
import GHC.Types.HpcInfo
import GHC.Types.Id
import GHC.Types.Id.Info
import GHC.Types.RepType
import GHC.Types.Basic
import GHC.Types.Var.Set ( isEmptyDVarSet )
import GHC.Types.Unique.FM
import GHC.Types.Name.Env

import GHC.Core.DataCon
import GHC.Core.TyCon
import GHC.Core.Multiplicity

import GHC.Unit.Module

import GHC.Utils.Error
import GHC.Utils.Outputable
import GHC.Utils.Panic

import GHC.SysTools.FileCleanup

import GHC.Data.Stream
import GHC.Data.OrdList
import GHC.Types.Unique.Map

import Control.Monad (when,void, forM_)
import GHC.Utils.Misc
import System.IO.Unsafe
import qualified Data.ByteString as BS
import Data.Maybe
import Control.Monad.Trans.State
import Control.Monad.Trans.Class

data CodeGenState = CodeGenState { codegen_used_info :: !(OrdList CmmInfoTable)
                                 , codegen_state :: !CgState }


codeGen :: DynFlags
        -> Module
        -> InfoTableProvMap
        -> [TyCon]
        -> CollectedCCs                -- (Local/global) cost-centres needing declaring/registering.
        -> [CgStgTopBinding]           -- Bindings to convert
        -> HpcInfo
        -> Stream IO CmmGroup (SDoc, ModuleLFInfos)       -- Output as a stream, so codegen can
                                       -- be interleaved with output

codeGen dflags this_mod ip_map@(InfoTableProvMap (UniqMap denv) _) data_tycons
        cost_centre_info stg_binds hpc_info
  = liftIO initC >>= \c -> flip evalStateT (CodeGenState mempty c) $ do  {     -- cg: run the code generator, and yield the resulting CmmGroup
              -- Using an IORef to store the state is a bit crude, but otherwise
              -- we would need to add a state monad layer.
        ; let cg :: FCode a -> StateT CodeGenState (Stream IO CmmGroup) a
              cg fcode = do
                (a, cmm) <- withTimingSilent dflags (text "STG -> Cmm") (`seq` ()) $ do
                         CodeGenState ts st <- get
                         let (a,st') = runC dflags this_mod st (getCmm fcode)

                         -- NB. stub-out cgs_tops and cgs_stmts.  This fixes
                         -- a big space leak.  DO NOT REMOVE!
                         -- This is observed by the #3294 test
                         let !used_info
                                | gopt Opt_InfoTableMap dflags = toOL (mapMaybe topInfoTable (snd a)) `mappend` ts
                                | otherwise = mempty
                         put $! CodeGenState used_info
                                  (st'{ cgs_tops = nilOL,
                                        cgs_stmts = mkNop
                                      })

                         return a
                lift $ yield cmm
                return a

               -- Note [codegen-split-init] the cmm_init block must come
               -- FIRST.  This is because when -split-objs is on we need to
               -- combine this block with its initialisation routines; see
               -- Note [pipeline-split-init].
        ; cg (mkModuleInit cost_centre_info this_mod hpc_info)

        ; mapM_ (cg . cgTopBinding dflags) stg_binds
                -- Put datatype_stuff after code_stuff, because the
                -- datatype closure table (for enumeration types) to
                -- (say) PrelBase_True_closure, which is defined in
                -- code_stuff
        ; let do_tycon tycon = do
                -- Generate a table of static closures for an
                -- enumeration type Note that the closure pointers are
                -- tagged.
                 when (isEnumerationTyCon tycon) $ cg (cgEnumerationTyCon tycon)
                 -- Emit normal info_tables, for data constructors defined in this module.
                 mapM_ (cg . cgDataCon DefinitionSite) (tyConDataCons tycon)

        ; mapM_ do_tycon data_tycons

        ; cg_id_infos <- cgs_binds . codegen_state <$> get


        -- Emit special info tables for everything used in this module
        -- This will only do something if  `-fdistinct-info-tables` is turned on.
        ; mapM_ (\(dc, ns) -> forM_ ns $ \(k, _ss) -> cg (cgDataCon (UsageSite this_mod k) dc)) (nonDetEltsUFM denv)

        ; used_info <- fromOL . codegen_used_info <$> get
        ; !foreign_stub <- cg (initInfoTableProv used_info ip_map this_mod)

          -- See Note [Conveying CAF-info and LFInfo between modules] in
          -- GHC.StgToCmm.Types
        ; let extractInfo info = (name, lf)
                where
                  !name = idName (cg_id info)
                  !lf = cg_lf info

              !generatedInfo
                | gopt Opt_OmitInterfacePragmas dflags
                = emptyNameEnv
                | otherwise
                = mkNameEnv (Prelude.map extractInfo (eltsUFM cg_id_infos))

        ; return (foreign_stub, generatedInfo)
        }

---------------------------------------------------------------
--      Top-level bindings
---------------------------------------------------------------

{- 'cgTopBinding' is only used for top-level bindings, since they need
to be allocated statically (not in the heap) and need to be labelled.
No unboxed bindings can happen at top level.

In the code below, the static bindings are accumulated in the
@MkCgState@, and transferred into the ``statics'' slot by @forkStatics@.
This is so that we can write the top level processing in a compositional
style, with the increasing static environment being plumbed as a state
variable. -}

cgTopBinding :: DynFlags -> CgStgTopBinding -> FCode ()
cgTopBinding dflags (StgTopLifted (StgNonRec id rhs))
  = do  { let (info, fcode) = cgTopRhs dflags NonRecursive id rhs
        ; fcode
        ; addBindC info
        }

cgTopBinding dflags (StgTopLifted (StgRec pairs))
  = do  { let (bndrs, rhss) = unzip pairs
        ; let pairs' = zip bndrs rhss
              r = unzipWith (cgTopRhs dflags Recursive) pairs'
              (infos, fcodes) = unzip r
        ; addBindsC infos
        ; sequence_ fcodes
        }

cgTopBinding dflags (StgTopStringLit id str) = do
  let label = mkBytesLabel (idName id)
  -- emit either a CmmString literal or dump the string in a file and emit a
  -- CmmFileEmbed literal.
  -- See Note [Embedding large binary blobs] in GHC.CmmToAsm.Ppr
  let isNCG    = backend dflags == NCG
      isSmall  = fromIntegral (BS.length str) <= binBlobThreshold dflags
      asString = binBlobThreshold dflags == 0 || isSmall

      (lit,decl) = if not isNCG || asString
        then mkByteStringCLit label str
        else mkFileEmbedLit label $ unsafePerformIO $ do
               bFile <- newTempName dflags TFL_CurrentModule ".dat"
               BS.writeFile bFile str
               return bFile
  emitDecl decl
  addBindC (litIdInfo (targetPlatform dflags) id mkLFStringLit lit)


cgTopRhs :: DynFlags -> RecFlag -> Id -> CgStgRhs -> (CgIdInfo, FCode ())
        -- The Id is passed along for setting up a binding...

cgTopRhs dflags _rec bndr (StgRhsCon _cc con mn _ts args)
  = cgTopRhsCon dflags bndr con mn (assertNonVoidStgArgs args)
      -- con args are always non-void,
      -- see Note [Post-unarisation invariants] in GHC.Stg.Unarise

cgTopRhs dflags rec bndr (StgRhsClosure fvs cc upd_flag args body)
  = ASSERT(isEmptyDVarSet fvs)    -- There should be no free variables
    cgTopRhsClosure (targetPlatform dflags) rec bndr cc upd_flag args body


---------------------------------------------------------------
--      Module initialisation code
---------------------------------------------------------------

mkModuleInit
        :: CollectedCCs         -- cost centre info
        -> Module
        -> HpcInfo
        -> FCode ()

mkModuleInit cost_centre_info this_mod hpc_info
  = do  { initHpc this_mod hpc_info
        ; initCostCentres cost_centre_info
        }


---------------------------------------------------------------
--      Generating static stuff for algebraic data types
---------------------------------------------------------------


cgEnumerationTyCon :: TyCon -> FCode ()
cgEnumerationTyCon tycon
  = do platform <- getPlatform
       emitRODataLits (mkLocalClosureTableLabel (tyConName tycon) NoCafRefs)
             [ CmmLabelOff (mkLocalClosureLabel (dataConName con) NoCafRefs)
                           (tagForCon platform con)
             | con <- tyConDataCons tycon]


cgDataCon :: ConInfoTableLocation -> DataCon -> FCode ()
-- Generate the entry code, info tables, and (for niladic constructor)
-- the static closure, for a constructor.
cgDataCon mn data_con
  = do  { MASSERT( not (isUnboxedTupleDataCon data_con || isUnboxedSumDataCon data_con) )
        ; profile <- getProfile
        ; platform <- getPlatform
        ; let
            (tot_wds, --  #ptr_wds + #nonptr_wds
             ptr_wds) --  #ptr_wds
              = mkVirtConstrSizes profile arg_reps

            nonptr_wds   = tot_wds - ptr_wds

            dyn_info_tbl =
              mkDataConInfoTable profile data_con mn False ptr_wds nonptr_wds

            -- We're generating info tables, so we don't know and care about
            -- what the actual arguments are. Using () here as the place holder.
            arg_reps :: [NonVoid PrimRep]
            arg_reps = [ NonVoid rep_ty
                       | ty <- dataConRepArgTys data_con
                       , rep_ty <- typePrimRep (scaledThing ty)
                       , not (isVoidRep rep_ty) ]

        ; emitClosureAndInfoTable platform dyn_info_tbl NativeDirectCall [] $
            -- NB: the closure pointer is assumed *untagged* on
            -- entry to a constructor.  If the pointer is tagged,
            -- then we should not be entering it.  This assumption
            -- is used in ldvEnter and when tagging the pointer to
            -- return it.
            -- NB 2: We don't set CC when entering data (WDP 94/06)
            do { tickyEnterDynCon
               ; ldvEnter (CmmReg nodeReg)
               ; tickyReturnOldCon (length arg_reps)
               ; void $ emitReturn [cmmOffsetB platform (CmmReg nodeReg) (tagForCon platform data_con)]
               }
                    -- The case continuation code expects a tagged pointer
        }
