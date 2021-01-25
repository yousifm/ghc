{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}

import Data.List
import Data.Data
import Data.Typeable
-- import GHC.Types.SrcLoc
import GHC.Types.Name.Occurrence
import GHC.Types.Name.Reader
import GHC hiding (moduleName)
import GHC.Driver.Ppr
import GHC.Driver.Session
import GHC.Hs.Dump
import GHC.Data.Bag
-- import GHC.Types.SourceText
-- import GHC.Hs.Exact hiding (ExactPrint())
-- import GHC.Utils.Outputable hiding (space)
import System.Environment( getArgs )
import System.Exit
import System.FilePath

import Types
import Utils
import ExactPrint
import Transform
import Parsers
import qualified Parsers as P
-- exactPrint = undefined
-- showPprUnsafe = undefined

import GHC.Parser.Lexer
import GHC.Data.FastString
import GHC.Types.SrcLoc
import GHC

-- ---------------------------------------------------------------------

tt :: IO ()
-- tt = testOneFile "/home/alanz/mysrc/git.haskell.org/ghc/_build/stage1/lib"
tt = testOneFile "/home/alanz/mysrc/git.haskell.org/worktree/exactprint/_build/stage1/lib"
 -- "cases/RenameCase1.hs" changeRenameCase1
 -- "cases/LayoutLet2.hs" changeLayoutLet2
 -- "cases/LayoutLet3.hs" changeLayoutLet3
 -- "cases/LayoutLet4.hs" changeLayoutLet3
 -- "cases/Rename1.hs" changeRename1
 -- "cases/Rename2.hs" changeRename2
 -- "cases/LayoutIn1.hs" changeLayoutIn1
 -- "cases/LayoutIn3.hs" changeLayoutIn3
 -- "cases/LayoutIn3a.hs" changeLayoutIn3
 -- "cases/LayoutIn3b.hs" changeLayoutIn3
 -- "cases/LayoutIn4.hs" changeLayoutIn4
 -- "cases/LocToName.hs" changeLocToName
 -- "cases/LetIn1.hs" changeLetIn1
 -- "cases/WhereIn4.hs" changeWhereIn4
 -- "cases/AddDecl1.hs" changeAddDecl1
 "cases/AddDecl2.hs" changeAddDecl2
 -- "cases/AddDecl3.hs" changeAddDecl3
 -- "cases/LocalDecls.hs" changeLocalDecls
 -- "cases/LocalDecls2.hs" changeLocalDecls2
 -- "cases/WhereIn3a.hs" changeWhereIn3a
 -- "cases/WhereIn3b.hs" changeWhereIn3b
 -- "cases/AddLocalDecl1.hs" addLocaLDecl1
 -- "cases/AddLocalDecl2.hs" addLocaLDecl2
 -- "cases/AddLocalDecl3.hs" addLocaLDecl3



-- exact = ppr

-- ---------------------------------------------------------------------

usage :: String
usage = unlines
    [ "usage: check-ppr (libdir) (file)"
    , ""
    , "where libdir is the GHC library directory (e.g. the output of"
    , "ghc --print-libdir) and file is the file to parse."
    ]

main :: IO()
main = do
  args <- getArgs
  case args of
   [libdir,fileName] -> testOneFile libdir fileName noChange
   _ -> putStrLn usage

deriving instance Data Token
deriving instance Data PsSpan
deriving instance Data BufSpan
deriving instance Data BufPos

testOneFile :: FilePath -> String -> Changer -> IO ()
testOneFile libdir fileName changer = do
       (p,toks) <- parseOneFile libdir fileName
       putStrLn $ "\n\ngot p" ++ showAst (take 4 $ reverse toks)
       let
         origAst = ppAst (pm_parsed_source p)
         anns'   = pm_annotations p
         -- pped    = pragmas ++ "\n" ++ (exactPrint $ pm_parsed_source p)
         pped    = exactPrint (pm_parsed_source p) anns'
         -- pragmas = getPragmas anns'

         newFile         = dropExtension fileName <.> "ppr"      <.> takeExtension fileName
         newFileChanged  = dropExtension fileName <.> "changed"  <.> takeExtension fileName
         newFileExpected = dropExtension fileName <.> "expected" <.> takeExtension fileName
         astFile        = fileName <.> "ast"
         newAstFile     = fileName <.> "ast.new"
         changedAstFile = fileName <.> "ast.changed"

       -- pped' <- exactprintWithChange changeRenameCase1 (pm_parsed_source p) anns'
       (pped', ast') <- exactprintWithChange libdir changer (pm_parsed_source p) anns'
       -- putStrLn $ "\n\nabout to writeFile"
       writeFile changedAstFile (ppAst ast')
       writeFile astFile origAst
       -- putStrLn $ "\n\nabout to pp"
       writeFile newFile        pped
       writeFile newFileChanged pped'

       -- putStrLn $ "anns':" ++ showPprUnsafe (apiAnnRogueComments anns')

       (p',_) <- parseOneFile libdir newFile

       let newAstStr :: String
           newAstStr = ppAst (pm_parsed_source p')
       writeFile newAstFile newAstStr
       expectedSource <- readFile newFileExpected
       changedSource  <- readFile newFileChanged

       -- putStrLn $ "\n\nanns':" ++ showPprUnsafe (apiAnnRogueComments anns')

       let
         origAstOk       = origAst == newAstStr
         changedSourceOk = expectedSource == changedSource
       if origAstOk && changedSourceOk
         then do
           -- putStrLn "ASTs matched"
           exitSuccess
         else if not origAstOk
           then do
             putStrLn "AST Match Failed"
             -- putStrLn "\n===================================\nOrig\n\n"
             -- putStrLn origAst
             putStrLn "\n===================================\nNew\n\n"
             putStrLn newAstStr
             exitFailure
           else do
             putStrLn "Changed AST Source Mismatch"
             putStrLn "\n===================================\nExpected\n\n"
             putStrLn expectedSource
             putStrLn "\n===================================\nChanged\n\n"
             putStrLn changedSource
             putStrLn "\n===================================\n"
             putStrLn $ show changedSourceOk
             exitFailure

ppAst ast = showSDocUnsafe $ showAstData BlankSrcSpanFile NoBlankApiAnnotations ast

parseOneFile :: FilePath -> FilePath -> IO (ParsedModule, [Located Token])
parseOneFile libdir fileName = do
       let modByFile m =
             case ml_hs_file $ ms_location m of
               Nothing -> False
               Just fn -> fn == fileName
       runGhc (Just libdir) $ do
         dflags <- getSessionDynFlags
         let dflags2 = dflags `gopt_set` Opt_KeepRawTokenStream
         _ <- setSessionDynFlags dflags2
         addTarget Target { targetId = TargetFile fileName Nothing
                          , targetAllowObjCode = True
                          , targetContents = Nothing }
         _ <- load LoadAllTargets
         graph <- getModuleGraph
         let
           modSum = case filter modByFile (mgModSummaries graph) of
                     [x] -> x
                     xs -> error $ "Can't find module, got:"
                              ++ show (map (ml_hs_file . ms_location) xs)
         pm <- GHC.parseModule modSum
         toks <- getTokenStream (ms_mod modSum)
         return (pm, toks)

         -- getTokenStream :: GhcMonad m => Module -> m [Located Token]

-- getPragmas :: ApiAnns -> String
-- getPragmas anns' = pragmaStr
--   where
--     tokComment (L _ (AnnBlockComment s)) = s
--     tokComment (L _ (AnnLineComment  s)) = s
--     tokComment _ = ""

--     comments' = map tokComment $ sortRealLocated $ apiAnnRogueComments anns'
--     pragmas = filter (\c -> isPrefixOf "{-#" c ) comments'
--     pragmaStr = intercalate "\n" pragmas

-- pp :: (Outputable a) => a -> String
-- pp a = showPpr unsafeGlobalDynFlags a

-- ---------------------------------------------------------------------

exactprintWithChange :: FilePath -> Changer -> ParsedSource -> ApiAnns -> IO (String, ParsedSource)
exactprintWithChange libdir f p anns = do
  debugM $ "exactprintWithChange:anns=" ++ showGhc (apiAnnRogueComments anns)
  (anns',p') <- f libdir anns p
  return (exactPrint p' anns', p')


-- First param is libdir
type Changer = FilePath -> (ApiAnns -> ParsedSource -> IO (ApiAnns,ParsedSource))

noChange :: Changer
noChange libdir ans parsed = return (ans,parsed)

changeRenameCase1 :: Changer
changeRenameCase1 libdir ans parsed = return (ans,rename "bazLonger" [((3,15),(3,18))] parsed)

changeLayoutLet2 :: Changer
changeLayoutLet2 libdir ans parsed = return (ans,rename "xxxlonger" [((7,5),(7,8)),((8,24),(8,27))] parsed)

changeLayoutLet3 :: Changer
changeLayoutLet3 libdir ans parsed = return (ans,rename "xxxlonger" [((7,5),(7,8)),((9,14),(9,17))] parsed)

changeLayoutIn1 :: Changer
changeLayoutIn1 libdir ans parsed = return (ans,rename "square" [((7,17),(7,19)),((7,24),(7,26))] parsed)

changeLayoutIn3 :: Changer
changeLayoutIn3 libdir ans parsed = return (ans,rename "anotherX" [((7,13),(7,14)),((7,37),(7,38)),((8,37),(8,38))] parsed)

changeLayoutIn4 :: Changer
changeLayoutIn4 libdir ans parsed = return (ans,rename "io" [((7,8),(7,13)),((7,28),(7,33))] parsed)

changeLocToName :: Changer
changeLocToName libdir ans parsed = return (ans,rename "LocToName.newPoint" [((20,1),(20,11)),((20,28),(20,38)),((24,1),(24,11))] parsed)


changeRename1 :: Changer
changeRename1 libdir ans parsed = return (ans,rename "bar2" [((3,1),(3,4))] parsed)

changeRename2 :: Changer
changeRename2 libdir ans parsed = return (ans,rename "joe" [((2,1),(2,5))] parsed)

rename :: (Data a) => String -> [(Pos, Pos)] -> a -> a
rename newNameStr spans' a
  = everywhere (mkT replaceRdr) a
  where
    newName = mkRdrUnqual (mkVarOcc newNameStr)

    cond :: SrcSpan -> Bool
    cond ln = ss2range ln `elem` spans'

    replaceRdr :: LocatedN RdrName -> LocatedN RdrName
    replaceRdr (L ln _)
        | cond (locA ln) = L ln newName
    replaceRdr x = x

-- ---------------------------------------------------------------------

changeWhereIn4 :: Changer
changeWhereIn4 libdir ans parsed
  = return (ans,everywhere (mkT replace) parsed)
  where
    replace :: LocatedN RdrName -> LocatedN RdrName
    replace (L ln _n)
      | ss2range (locA ln) == ((12,16),(12,17)) = L ln (mkRdrUnqual (mkVarOcc "p_2"))
    replace x = x

-- ---------------------------------------------------------------------

changeLetIn1 :: Changer
changeLetIn1 libdir ans parsed
  = return (ans,everywhere (mkT replace) parsed)
  where
    replace :: HsExpr GhcPs -> HsExpr GhcPs
    replace (HsLet an localDecls expr)
      =
         let (HsValBinds x (ValBinds xv bagDecls sigs)) = localDecls
             decls@(l1:l2:ls) = reverse $ bagToList bagDecls
             l2' = remove l2 l1
             bagDecls' = listToBag $ reverse (l2':ls)
         in (HsLet an (HsValBinds x (ValBinds xv bagDecls' sigs)) expr)

    replace x = x
-- ---------------------------------------------------------------------

-- | Add a declaration to AddDecl
changeAddDecl1 :: Changer
changeAddDecl1 libdir ans top = do
  Right (declAnns, decl) <- withDynFlags libdir (\df -> parseDecl df "<interactive>" "nn = n2")
  let decl' = setEntryDP' decl (DP (2,0))

  let (p',(ans',_),_) = runTransform mempty doAddDecl
      doAddDecl = everywhereM (mkM replaceTopLevelDecls) top
      replaceTopLevelDecls :: ParsedSource -> Transform ParsedSource
      replaceTopLevelDecls m = insertAtStart m decl'
  return (ans,p')

changeAddDecl2 :: Changer
changeAddDecl2 libdir ans top = do
  Right (declAnns, decl) <- withDynFlags libdir (\df -> parseDecl df "<interactive>" "nn = n2")
  let decl' = setEntryDP' decl (DP (2,0))
  let top' = anchorEof top

  let (p',(ans',_),_) = runTransform mempty doAddDecl
      doAddDecl = everywhereM (mkM replaceTopLevelDecls) top'
      replaceTopLevelDecls :: ParsedSource -> Transform ParsedSource
      replaceTopLevelDecls m = insertAtEnd m decl'
  return (ans,p')

changeAddDecl3 :: Changer
changeAddDecl3 libdir ans top = do
  Right (declAnns, decl) <- withDynFlags libdir (\df -> parseDecl df "<interactive>" "nn = n2")
  let decl' = setEntryDP' decl (DP (2,0))

  let (p',(ans',_),_) = runTransform mempty doAddDecl
      doAddDecl = everywhereM (mkM replaceTopLevelDecls) top
      f d (l1:l2:ls) = l1:d:l2':ls
        where
          l2' = setEntryDP' l2 (DP (2,0))
      replaceTopLevelDecls :: ParsedSource -> Transform ParsedSource
      replaceTopLevelDecls m = insertAt f m decl'
  return (ans,p')

-- ---------------------------------------------------------------------

-- | Add a local declaration with signature to LocalDecl
changeLocalDecls :: Changer
changeLocalDecls libdir ans (L l p) = do
  Right (declAnns, d@(L ld (ValD _ decl))) <- withDynFlags libdir (\df -> parseDecl df "decl" "nn = 2")
  Right (sigAnns, s@(L ls (SigD _ sig)))   <- withDynFlags libdir (\df -> parseDecl df "sig"  "nn :: Int")
  let decl' = setEntryDP' (L ld decl) (DP (1, 0))
  let  sig' = setEntryDP' (L ls sig) (DP (0, 0))
  let (p',(ans',_),_w) = runTransform mempty doAddLocal
      doAddLocal = everywhereM (mkM replaceLocalBinds) p
      replaceLocalBinds :: LMatch GhcPs (LHsExpr GhcPs)
                        -> Transform (LMatch GhcPs (LHsExpr GhcPs))
      replaceLocalBinds m@(L lm (Match an mln pats (GRHSs _ rhs (HsValBinds van (ValBinds _ binds sigs))))) = do
        let oldDecls = sortLocatedA $ map wrapDecl (bagToList binds) ++ map wrapSig sigs
        let decls = s:d:oldDecls
        let oldDecls' = captureLineSpacing oldDecls
        let oldBinds     = concatMap decl2Bind oldDecls'
            (os:oldSigs) = concatMap decl2Sig  oldDecls'
            os' = setEntryDP' os (DP (2, 0))
        let sortKey = captureOrder' decls
        let binds' = (HsValBinds van
                          (ValBinds sortKey (listToBag $ decl':oldBinds)
                                          (sig':os':oldSigs)))
        return (L lm (Match an mln pats (GRHSs noExtField rhs binds')))
      replaceLocalBinds x = return x
  return (ans,L l p')

-- ---------------------------------------------------------------------

-- | Add a local declaration with signature to LocalDecl, where there was no
-- prior local decl. So it adds a "where" annotation.
changeLocalDecls2 :: Changer
changeLocalDecls2 libdir ans (L l p) = do
  Right (_, d@(L ld (ValD _ decl))) <- withDynFlags libdir (\df -> parseDecl df "decl" "nn = 2")
  Right (_, s@(L ls (SigD _ sig)))  <- withDynFlags libdir (\df -> parseDecl df "sig"  "nn :: Int")
  let decl' = setEntryDP' (L ld decl) (DP (1, 0))
  let  sig' = setEntryDP' (L ls  sig) (DP (0, 2))
  let (p',(ans',_),_w) = runTransform mempty doAddLocal
      doAddLocal = everywhereM (mkM replaceLocalBinds) p
      replaceLocalBinds :: LMatch GhcPs (LHsExpr GhcPs)
                        -> Transform (LMatch GhcPs (LHsExpr GhcPs))
      replaceLocalBinds m@(L lm (Match ma mln pats (GRHSs _ rhs EmptyLocalBinds{}))) = do
        newSpan <- uniqueSrcSpanT
        let anc = (Anchor (rs newSpan) (MovedAnchor (DP (1,2))))
        let an = ApiAnn anc
                        (AnnList (Just anc) Nothing Nothing
                                 [(undeltaSpan (rs newSpan) AnnWhere (DP (0,0)))] [])
                        noCom
        let decls = [s,d]
        let sortKey = captureOrder' decls
        let binds = (HsValBinds an (ValBinds sortKey (listToBag $ [decl'])
                                    [sig']))
        return (L lm (Match ma mln pats (GRHSs noExtField rhs binds)))
      replaceLocalBinds x = return x
  return (ans,L l p')

-- ---------------------------------------------------------------------

-- | Check that balanceCommentsList is idempotent
changeWhereIn3a :: Changer
changeWhereIn3a libdir ans (L l p) = do
  let decls0 = hsmodDecls p
      (decls,(ans',_),w) = runTransform mempty (balanceCommentsList decls0)
      (d0:_:d1:d2:_) = decls
      -- d0 : sumSquares
      -- skip signature
      -- d1 : sq
      -- d2 : anotherFun
  debugM $ unlines w
  debugM $ "changeWhereIn3a:d1:" ++ showAst d1
  let p2 = p { hsmodDecls = decls}
  return (ans,L l p2)

-- ---------------------------------------------------------------------

changeWhereIn3b :: Changer
changeWhereIn3b libdir ans (L l p) = do
  let decls0 = hsmodDecls p
      (decls,(ans',_),w) = runTransform mempty (balanceCommentsList decls0)
      (d0:_:d1:d2:_) = decls
      -- d0 : sumSquares
      -- skip signature
      -- d1 : sq
      -- d2 : anotherFun
      d0' = setEntryDP' d0 (DP (2, 0))
      d1' = setEntryDP' d1 (DP (2, 0))
      d2' = setEntryDP' d2 (DP (2, 0))
      decls' = d2':d1':d0':(tail decls)
  debugM $ unlines w
  debugM $ "changeWhereIn3b:d1':" ++ showAst d1'
  let p2 = p { hsmodDecls = decls'}
  return (ans,L l p2)

-- ---------------------------------------------------------------------

addLocaLDecl1 :: Changer
addLocaLDecl1 libdir ans lp = do
  Right (_, (L ld (ValD _ decl))) <- withDynFlags libdir (\df -> parseDecl df "decl" "nn = 2")
  -- let declAnns' = setPrecedingLines newDecl 1 4 declAnns
  let decl' = setEntryDP' (L ld decl) (DP (1, 4))
      doAddLocal = do
        (d1:d2:d3:_) <- hsDecls lp
        (d1'',d2') <- balanceComments d1 d2
        (d1',_) <- modifyValD (getLocA d1'') d1'' $ \_m d -> do
          return ((wrapDecl decl' : d),Nothing)
        replaceDecls lp [d1', d2', d3]

  (lp',(ans',_),w) <- runTransformT mempty doAddLocal
  -- putStrLn $ "log:\n" ++ intercalate "\n" _w
  debugM $ "addLocaLDecl1:" ++ intercalate "\n" w
  return (ans,lp')

-- ---------------------------------------------------------------------

addLocaLDecl2 :: Changer
addLocaLDecl2 libdir ans lp = do
  Right (_, newDecl@(L ld (ValD _ decl))) <- withDynFlags libdir (\df -> parseDecl df "decl" "nn = 2")
  let
      doAddLocal = do
         -- tlDecs <- hsDecls lp
         -- let parent = head tlDecs
         -- balanceComments parent (head $ tail tlDecs)
         (d1:d2:_) <- hsDecls lp
         (d1'',d2') <- balanceComments d1 d2

         (parent',_) <- modifyValD (getLocA d1) d1'' $ \_m (d:ds) -> do
           newDecl' <- transferEntryDP' d newDecl
           let d' = setEntryDP' d (DP (1, 0))
           return ((newDecl':d':ds),Nothing)

         replaceDecls lp [parent',d2']
         -- replaceDecls lp [d1'',d2']

  (lp',(ans',_),_w) <- runTransformT mempty doAddLocal
  debugM $ "log:[\n" ++ intercalate "\n" _w ++ "]log end\n"
  return (ans,lp')

-- ---------------------------------------------------------------------

addLocaLDecl3 :: Changer
addLocaLDecl3 libdir ans lp = do
  Right (_, newDecl@(L ld (ValD _ decl))) <- withDynFlags libdir (\df -> parseDecl df "decl" "nn = 2")
  let
      doAddLocal = do
         -- logDataWithAnnsTr "parsed:" lp
         -- logDataWithAnnsTr "newDecl:" newDecl
         -- tlDecs <- hsDecls lp
         -- let parent = head tlDecs
         -- balanceComments parent (head $ tail tlDecs)

         -- (parent',_) <- modifyValD (getLoc parent) parent $ \m decls -> do
         --   setPrecedingLinesT newDecl 1 0
         --   moveTrailingComments m (last decls)
         --   return ((decls++[newDecl]),Nothing)

         -- replaceDecls lp (parent':tail tlDecs)
         (d1:d2:_) <- hsDecls lp
         (d1'',d2') <- balanceComments d1 d2

         (parent',_) <- modifyValD (getLocA d1) d1'' $ \_m (d:ds) -> do
           let newDecl' = setEntryDP' newDecl (DP (1, 0))
           let d' = setEntryDP' d (DP (0,0))
           return (((d':ds) ++ [newDecl']),Nothing)
           -- return (d':ds,Nothing)

         replaceDecls lp [parent',d2']

  (lp',(ans',_),_w) <- runTransformT mempty doAddLocal
  -- putStrLn $ "log\n" ++ intercalate "\n" _w
  debugM $ "log:[\n" ++ intercalate "\n" _w ++ "]log end\n"
  return (ans,lp')


-- ---------------------------------------------------------------------
-- Next section to be moved to the appropriate library

remove :: (Monoid t) => LocatedAn t a -> LocatedAn u b -> LocatedAn t a
remove (L (SrcSpanAnn ApiAnnNotUsed l) v) lb
  = L (SrcSpanAnn (ApiAnn (Anchor (realSrcSpan l) (DeletedAnchor $ locatedAnAnchor lb)) mempty noCom) l) v
remove (L (SrcSpanAnn (ApiAnn a an cs) l) v) lb
  = L (SrcSpanAnn (ApiAnn (Anchor (anchor a) (DeletedAnchor $ locatedAnAnchor lb)) an cs) l) v

locatedAnAnchor :: LocatedAn a t -> RealSrcSpan
locatedAnAnchor (L (SrcSpanAnn ApiAnnNotUsed l) _) = realSrcSpan l
locatedAnAnchor (L (SrcSpanAnn (ApiAnn a _ _) _) _) = anchor a

-- End of section to be moved to the appropriate library
-- ---------------------------------------------------------------------


-- ---------------------------------------------------------------------
-- From SYB

-- | Apply transformation on each level of a tree.
--
-- Just like 'everything', this is stolen from SYB package.
everywhere :: (forall a. Data a => a -> a) -> (forall a. Data a => a -> a)
everywhere f = f . gmapT (everywhere f)

-- | Create generic transformation.
--
-- Another function stolen from SYB package.
mkT :: (Typeable a, Typeable b) => (b -> b) -> (a -> a)
mkT f = case cast f of
    Just f' -> f'
    Nothing -> id

-- ---------------------------------------------------------------------
