{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

-- | Types for the Constructed Product Result lattice. "GHC.Core.Opt.CprAnal"
-- and "GHC.Core.Opt.WorkWrap.Utils" are its primary customers via
-- 'GHC.Types.Id.idCprInfo'.
module GHC.Types.Cpr (
    Cpr, botCpr, topCpr, lubCpr, appCpr, lamCpr, asConCpr,
    expandConFieldsCpr, pruneDeepCpr, dropNonBotCpr,
    CprSig, topCprSig, botCprSig, mkFunCprSig, mkPlainCprSig, seqCprSig,
    cprTransformSig, cprTransformDataConWork, argCprsFromStrictSig
  ) where

#include "HsVersions.h"

import GHC.Prelude

import GHC.Builtin.Names ( Unique, runRWKey )
import GHC.Types.Basic
import GHC.Types.Demand
import GHC.Types.Termination
import GHC.Types.Unbox
import GHC.Core.DataCon
import GHC.Core.Type
import GHC.Core.Multiplicity
import GHC.Utils.Binary
import GHC.Utils.Misc
import GHC.Utils.Outputable
import GHC.Data.Maybe

import Data.Coerce

import GHC.Driver.Ppr
_ = pprTrace -- Tired of commenting out GHC.Driver.Ppr

--------
-- * Cpr

newtype Cpr
  = Cpr_ (CloShape Cpr)
  deriving (Binary, Eq)

-- | Normalises the nested CPR info according to
-- > TopSh === LamSh topCpr
-- Because CPR only cares if ultimately we see a data constructor. A 'Lam' can
-- be eta-expanded independently of whether it cancels away in the body by way
-- of an 'App'.
normCprShape :: CloShape Cpr -> CloShape Cpr
normCprShape (LamSh cpr) | cpr == topCpr = TopSh
normCprShape sh                          = sh

pattern Cpr :: CloShape Cpr -> Cpr
pattern Cpr sh <- (Cpr_ sh)
  where
    Cpr sh = Cpr_ (normCprShape sh)
{-# COMPLETE Cpr #-}

botCpr :: Cpr
botCpr = Cpr BotSh

topCpr :: Cpr
topCpr = Cpr TopSh

lubCpr :: Cpr -> Cpr -> Cpr
lubCpr (Cpr sh1) (Cpr sh2) = Cpr (lubCloShape lubCpr sh1 sh2)

conCpr :: DataCon -> [Cpr] -> Cpr
conCpr dc cprs = Cpr (ConSh (dataConTag dc) cprs)

pruneDeepCpr :: Int -> Cpr -> Cpr
pruneDeepCpr depth = coerce (pruneCloShape pruneDeepCpr depth)

-- | Split for the given 'ConTag' if the 'Cpr' is of 'ConSh' or 'BotSh'.
splitConCpr :: ConTag -> Int -> Cpr -> Maybe [Cpr]
splitConCpr tag arty (Cpr sh) = splitConSh botCpr tag arty sh

expandConFieldsCpr :: DataCon -> Cpr -> [Cpr]
expandConFieldsCpr dc c =
  splitConCpr (dataConTag dc) (dataConRepArity dc) c
    `orElse` replicate (dataConRepArity dc) topCpr

splitLamCpr :: Cpr -> Maybe Cpr
splitLamCpr (Cpr BotSh)     = Just botCpr
splitLamCpr (Cpr (LamSh c)) = Just c
splitLamCpr _               = Nothing

appCpr :: Cpr -> Cpr
appCpr cpr
  | Just cpr' <- splitLamCpr cpr = cpr'
  | otherwise                    = topCpr

appsCpr :: Arity -> Cpr -> Cpr
appsCpr n cpr = iterate appCpr cpr !! n

lamCpr :: Cpr -> Cpr
lamCpr cpr = Cpr (LamSh cpr)

lamsCpr :: Arity -> Cpr -> Cpr
lamsCpr n cpr = iterate lamCpr cpr !! n

dropNonBotCpr :: Cpr -> Cpr
-- See Note [CPR for thunks]
dropNonBotCpr c
  | is_bot_fun c = c -- Don't forget bot => error thunks should have CPR
  | otherwise    = topCpr
  where
    is_bot_fun (Cpr BotSh)     = True
    is_bot_fun (Cpr (LamSh c)) = is_bot_fun c
    is_bot_fun _               = False

-- | Trim away excess 'LamSh'.
trimLam :: Cpr -> Cpr
-- See Note [Arity trimming for CPR signatures]
trimLam (Cpr LamSh{}) = topCpr
trimLam cpr           = cpr

-- | Trims deep CPR information as soon as there is a single 'MightDiverge'.
trimToTerm :: Term -> Cpr -> Cpr
-- See Note [Trimming CPR signatures according to Term]
trimToTerm term cpr
  -- No further MightDiverge in the way, stop trimming
  | term == botTerm
  = cpr
  -- Handle bot CPR. Important for GHC.Utils.Panic.panic
  | Term Terminates _ <- term
  , cpr == botCpr
  = botCpr
  -- Handle (expansion to) ConSh
  | Term Terminates (ConSh t terms) <- term
  , Just cprs <- splitConCpr t (length terms) cpr
  = Cpr (ConSh t (zipWith trimToTerm terms cprs))
  | Cpr (ConSh t cprs) <- cpr
  , (Terminates, terms) <- splitConTerm t (length cprs) term
  = Cpr (ConSh t (zipWith trimToTerm terms cprs))
  -- Handle (expansion to) LamSh
  | Term Terminates (LamSh t) <- term
  , Just c <- splitLamCpr cpr
  = Cpr (LamSh (trimToTerm t c))
  | Cpr (LamSh c) <- cpr
  , (Terminates, t) <- splitLamTerm term
  = Cpr (LamSh (trimToTerm t c))
  -- Otherwise top
  | otherwise
  = topCpr

seqCpr :: Cpr -> ()
seqCpr = coerce (seqCloShape seqCpr)

asConCpr :: Cpr -> Maybe (ConTag, [Cpr])
-- This is the key function consulted by WW
asConCpr (Cpr (ConSh t cprs)) = Just (t, cprs)
asConCpr _                    = Nothing

-----------
-- * CprSig

-- | Not just 'Cpr', because it lacks 'idArity' many 'LamSh' (see 'Sig').
-- We also need to take some care to trim CPR results from function bodies when
-- we turn them into a 'CprSig'. See 'mkFunCprSig'.
type CprSig = Sig Cpr

topCprSig :: CprSig
topCprSig = Sig topCpr

botCprSig :: CprSig
botCprSig = Sig botCpr

seqCprSig :: CprSig -> ()
seqCprSig = coerce seqCpr

-- | Turns a 'Cpr' of a function into a signature that is unleashable
-- at call sites of the particular 'Arity' and minimum call 'Demand'.
--
-- See Note [Trimming CPR signatures according to Term]
-- and Note [Improving CPR by considering strictness demand from call sites],
-- as well as Note [Arity trimming for CPR signatures],
-- all in "GHC.Core.Opt.CprAnal".
mkFunCprSig :: Arity -> Demand -> Term -> Cpr -> CprSig
mkFunCprSig arty fun_demand rhs_term rhs_cpr =
  -- pprTrace "mkFunCprSig" (vcat [ppr arty, ppr fun_demand, ppr body_sd, ppr body_term, ppr body_cpr, ppr body_term', ppr final_cpr]) $
  Sig final_cpr
  where
    -- See Note [Improving CPR by considering strictness demand from call sites]
    -- Figure out the *least sub-demand* put on the function body by all call sites.
    -- Sub-demand, because we can assume at least seq demand on the body.
    (_card1 :* fn_sd) = fun_demand -- how the function was called
    (_card2, body_sd) = peelManyCalls arty fn_sd
    -- body_sd is now the least demand put on the fun body by a single, sat call
    body_term         = appsTerm arty rhs_term
    body_cpr          = appsCpr  arty rhs_cpr
    (_, body_term')   = forceTerm body_sd body_term -- combine with body_sd
    -- See Note [Arity trimming for CPR signatures]
    -- See Note [Trimming CPR signatures according to Term]
    final_cpr = trimToTerm body_term' (trimLam body_cpr)

-- | Takes a 'Cpr' for an expression of the given 'Arity' and turn it into a
-- signature. Unlike 'mkFunCprSig', this does no smart processing of how much
-- of the given 'Cpr' is actually available at use sites.
mkPlainCprSig :: Arity -> Cpr -> CprSig
-- Strip the arity many (and thus boring) LamSh's
mkPlainCprSig = coerce appsCpr

-- | Compared to 'termTransformSig', this one is not higher-order!
-- ... Except for runRW#.
cprTransformSig :: Unique -> Arity -> CprSig -> [Cpr] -> Cpr
cprTransformSig id_uniq  _arity _sig      arg_cprs
  | id_uniq == runRWKey -- `runRW  :: (State# RealWorld -> o) -> o`
  , [arg] <- arg_cprs   -- `arg    :: State# RealWorld -> o`        has `L1(,1)`
  = appCpr arg          -- `result :: o`                            has  `1(,1)`
cprTransformSig _id_uniq arity  (Sig cpr) _arg_cprs
  = lamsCpr arity cpr

-- | Get a 'Cpr' for a 'DataCon', given 'Cpr's for its fields.
cprTransformDataConWork :: DataCon -> [Cpr] -> Cpr
-- What about DataCon *wrappers*? See Note [CPR for DataCon wrappers]
cprTransformDataConWork con args
  | null (dataConExTyCoVars con)  -- No existentials
  , wkr_arity <= mAX_CPR_SIZE
  , args `lengthIs` wkr_arity
  -- , pprTrace "cprTransformDataConWork" (ppr con <+> ppr wkr_arity <+> ppr args) True
  = lamsCpr wkr_arity (conCpr con args)
  | otherwise
  = topCpr
  where
    wkr_arity = dataConRepArity con

mAX_CPR_SIZE :: Arity
mAX_CPR_SIZE = 10
-- We do not treat very big tuples as CPR-ish:
--      a) for a start we get into trouble because there aren't
--         "enough" unboxed tuple types (a tiresome restriction,
--         but hard to fix),
--      b) more importantly, big unboxed tuples get returned mainly
--         on the stack, and are often then allocated in the heap
--         by the caller.  So doing CPR for them may in fact make
--         things worse.

-- | Produces 'Cpr's according to how strict argument types will be unboxed.
-- Examples:
--
--   * A head-strict demand `S` on `Int` would translate to `c1(*)`
--   * A tuple demand `S(S,L)` on `(Int, Bool)` would translate to `c1(c1(*),*)`
--   * A tuple demand `S(S,L)` on `(a , Bool)` would translate to `c1(*,*)`,
--     because the unboxing strategy would not unbox the `a`.
argCprsFromStrictSig :: UnboxingStrategy Demand -> [Type] -> StrictSig -> [Cpr]
argCprsFromStrictSig want_to_unbox arg_tys sig
  = zipWith go arg_tys (fst (splitStrictSig sig))
  where
    go ty dmd
      | Unbox (DataConPatContext { dcpc_dc = dc, dcpc_tc_args = tc_args }) dmds
          <- want_to_unbox ty dmd
      -- No existentials; see Note [Which types are unboxed?])
      -- Otherwise we'd need to call dataConRepInstPat here and thread a UniqSupply
      , null (dataConExTyCoVars dc)
      , let arg_tys = map scaledThing (dataConInstArgTys dc tc_args)
      = conCpr dc (zipWith go arg_tys dmds)
      | otherwise
      = topCpr

-- | Formats `lamCpr (conCpr 3 [conCpr 5 [topCpr], conCpr 2 [topCpr, botCpr])`
--   as      `L3(5,2(,b))`.
instance Outputable Cpr where
  ppr (Cpr l) = pprCloShape (char 'b') (any (/= topCpr)) l
