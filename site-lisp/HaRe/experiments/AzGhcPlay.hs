{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- Sample refactoring based on ifToCase
import Bag
import Bag(Bag,bagToList)
import Data.Generics
import FastString(FastString)
import GHC.Paths ( libdir )
import GHC.SYB.Utils
import RdrName
import OccName
import qualified OccName(occNameString)


-----------------

import qualified Data.Generics.Schemes as SYB
import qualified Data.Generics.Aliases as SYB
import qualified GHC.SYB.Utils         as SYB

import Var
import qualified CoreFVs               as GHC
import qualified CoreSyn               as GHC
import qualified DynFlags              as GHC
import qualified ErrUtils              as GHC
import qualified Exception             as GHC
import qualified FastString            as GHC
import qualified GHC                   as GHC
import qualified HscTypes              as GHC
import qualified Lexer                 as GHC
import qualified MonadUtils            as GHC
import qualified Outputable            as GHC
import qualified SrcLoc                as GHC
import qualified StringBuffer          as GHC

import GHC.Paths ( libdir )

-----------------

import Language.Haskell.Refact.Utils
import Language.Haskell.Refact.Utils.GhcUtils
import Language.Haskell.Refact.Utils.LocUtils
import Language.Haskell.Refact.Utils.Monad
import Language.Haskell.Refact.Utils.TokenUtils
import Language.Haskell.Refact.Utils.TypeUtils
import qualified Language.Haskell.Refact.Case as GhcRefacCase
import qualified Language.Haskell.Refact.SwapArgs as GhcSwapArgs

import Control.Monad.State

import Control.Applicative
import Data.Data
import Data.IORef
import System.Directory
import System.FilePath
import qualified Data.Map as Map

-- import Language.Haskell.Refact.Utils.GhcUtils


-- targetFile = "./refactorer/" ++ targetMod ++ ".hs"

-- targetFile = "./test/testdata/" ++ targetMod ++ ".hs"
-- targetMod = "FreeAndDeclared/Declare"

--targetFile = "../test/testdata/" ++ targetMod ++ ".hs"

-- ++AZ++ targetFile = "./test/testdata/TypeUtils/" ++ targetMod ++ ".hs"
--targetFile = "./" ++ targetMod ++ ".hs"
-- targetMod = "SwapArgs/B"
-- targetMod = "Ole"
-- ++AZ++ targetMod = "Empty"

targetFile = "./test/testdata/" ++ targetMod ++ ".hs" -- ++AZ++
-- targetMod = "Demote/WhereIn6"                                       -- ++AZ++
-- targetMod = "MoveDef/Md1"                                       -- ++AZ++
-- targetMod = "Demote/WhereIn2"                                       -- ++AZ++
-- targetMod = "Demote/PatBindIn1"                                       -- ++AZ++
targetMod = "BCpp"                                       -- ++AZ++

main = putStrLn "main"

p1 =
  do
    toks <- lexStringToRichTokens (GHC.mkRealSrcLoc (GHC.mkFastString "foo") 0 0) "if (1) then x else y"
    putStrLn $ showToks toks


-- data HsExpr id
--   ...
--   HsIf (Maybe (SyntaxExpr id)) (LHsExpr id) (LHsExpr id) (LHsExpr id)
--                                  ^1            ^2           ^3
--   ...
--  HsCase (LHsExpr id) (MatchGroup id)
--            ^1

-- data MatchGroup id
--   MatchGroup [LMatch id] PostTcType
-- type LMatch id = Located (Match id)
-- data Match id
--   Match [LPat id] (Maybe (LHsType id)) (GRHSs id)

getStuff =
#if __GLASGOW_HASKELL__ > 704
    GHC.defaultErrorHandler GHC.defaultFatalMessager GHC.defaultFlushOut $ do
#else
    GHC.defaultErrorHandler GHC.defaultLogAction $ do
#endif
      GHC.runGhc (Just libdir) $ do
        dflags <- GHC.getSessionDynFlags
        let dflags' = foldl GHC.xopt_set dflags
                           [GHC.Opt_Cpp, GHC.Opt_ImplicitPrelude, GHC.Opt_MagicHash]

            dflags'' = dflags' { GHC.importPaths = ["./test/testdata/","../test/testdata/"] }

            dflags''' = dflags'' { GHC.hscTarget = GHC.HscInterpreted,
                                   GHC.ghcLink =  GHC.LinkInMemory }

        GHC.setSessionDynFlags dflags'''
        GHC.liftIO $ putStrLn $ "dflags set"

        target <- GHC.guessTarget targetFile Nothing
        GHC.setTargets [target]
        GHC.liftIO $ putStrLn $ "targets set"
        GHC.load GHC.LoadAllTargets -- Loads and compiles, much as calling make
        GHC.liftIO $ putStrLn $ "targets loaded"
        -- modSum <- GHC.getModSummary $ GHC.mkModuleName "B"
        -- modSum <- GHC.getModSummary $ GHC.mkModuleName "FreeAndDeclared.Declare"
        -- modSum <- GHC.getModSummary $ GHC.mkModuleName "SwapArgs.B"
        -- modSum <- GHC.getModSummary $ GHC.mkModuleName "Ole"
        -- ++AZ++ modSum <- GHC.getModSummary $ GHC.mkModuleName targetMod 
        -- modSum <- GHC.getModSummary $ GHC.mkModuleName "Demote.WhereIn6"
        -- modSum <- GHC.getModSummary $ GHC.mkModuleName "MoveDef.Md1"
        -- modSum <- GHC.getModSummary $ GHC.mkModuleName "Demote.WhereIn2"
        -- modSum <- GHC.getModSummary $ GHC.mkModuleName "Demote.PatBindIn1"
        modSum <- GHC.getModSummary $ GHC.mkModuleName "BCpp"
        GHC.liftIO $ putStrLn $ "got modsummary"
        p <- GHC.parseModule modSum
        GHC.liftIO $ putStrLn $ "parsed"

        t <- GHC.typecheckModule p
        GHC.liftIO $ putStrLn $ "type checked"
        d <- GHC.desugarModule t
        l <- GHC.loadModule d
        n <- GHC.getNamesInScope
        -- c <- return $ GHC.coreModule d
        c <- return $ GHC.coreModule d

#if __GLASGOW_HASKELL__ > 704
        GHC.setContext [GHC.IIModule (GHC.moduleName $ GHC.ms_mod modSum)]
#else
        GHC.setContext [GHC.IIModule (                 GHC.ms_mod modSum)]
#endif

        -- GHC.setContext [GHC.IIModule (GHC.ms_mod modSum)]
        inscopes <- GHC.getNamesInScope
        GHC.liftIO $ putStrLn $ "got inscopes"


        g <- GHC.getModuleGraph
        gs <- mapM GHC.showModule g
        GHC.liftIO (putStrLn $ "modulegraph=" ++ (show gs))
        -- return $ (parsedSource d,"/n-----/n",  typecheckedSource d, "/n-=-=-=-=-=-=-/n", modInfoTyThings $ moduleInfo t)
        -- return $ (parsedSource d,"/n-----/n",  typecheckedSource d, "/n-=-=-=-=-=-=-/n")
        -- return $ (typecheckedSource d)

        -- res <- getRichTokenStream (ms_mod modSum)
        -- return $ showRichTokenStream res

        {-
        let ps = convertSource $ pm_parsed_source p
        let res = showData Parser 4 ps
        -- let res = showPpr ps
        return res
        -}
        -- let p' = processParsedMod ifToCase t
        -- GHC.liftIO (putStrLn . showParsedModule $ t)
        -- GHC.liftIO (putStrLn . showParsedModule $ p')
        -- GHC.liftIO (putStrLn $ showGhc $ GHC.tm_typechecked_source p')

        let ps  = GHC.pm_parsed_source p
        GHC.liftIO $ putStrLn $ "got parsed source"
        -- GHC.liftIO (putStrLn $ SYB.showData SYB.Parser 0 ps)
        -- GHC.liftIO (putStrLn $ show (modIsExported ps))
        -- _ <- processVarUniques t

        -- Suspect bug getting tokens for cpp source
        saf@(srcFile,src,flags) <- getModuleSourceAndFlags (GHC.ms_mod modSum)
        GHC.liftIO $ putStrLn $ "got saf:" ++ show (srcFile,src)
        GHC.liftIO $ putStrLn $ "got src:[" ++ sbufToString src ++ "]"
        GHC.liftIO $ putStrLn $ "got saf:" ++ show (srcFile,src)

        df <- GHC.getSessionDynFlags
        d <- GHC.liftIO $ getTempDir df
        GHC.liftIO $ putStrLn $ "temp dir=:" ++ show (d)
        fileList <- GHC.liftIO $ getDirectoryContents d
        GHC.liftIO $ putStrLn $ "temp dir files=:" ++ show (fileList)
        let suffix = "hscpp"

        let cppFiles = filter (\f -> getSuffix f == suffix) fileList
        GHC.liftIO $ putStrLn $ "temp dir hscpp files=:" ++ show (cppFiles)
        origNames <- GHC.liftIO $ mapM getOriginalFile $ map (\f -> d </> f) cppFiles
        GHC.liftIO $ putStrLn $ "temp dir orig names=:" ++ show (origNames)
        let tmpFile = head $ filter (\(o,_) -> o == srcFile) origNames
        GHC.liftIO $ putStrLn $ "temp dir tmpFile=:" ++ show (tmpFile)
        buf <- GHC.liftIO $ GHC.hGetStringBuffer $ snd tmpFile
        GHC.liftIO $ putStrLn $ "got buf:[" ++ sbufToString buf ++ "]"

        strSrcWithHead <- GHC.liftIO $ readFile $ snd tmpFile
        let strSrc = unlines $ drop 3 $ lines strSrcWithHead
        let strSrcBuf = GHC.stringToStringBuffer strSrc

        GHC.liftIO $ putStrLn $ "got strSrcBuf:[" ++ sbufToString strSrcBuf ++ "]"

        let startLoc = GHC.mkRealSrcLoc (GHC.mkFastString srcFile) 1 1
        tt <- case GHC.lexTokenStream src startLoc flags of
                GHC.POk _ ts  -> return ts
                GHC.PFailed span err ->
                   do -- dflags <- GHC.getDynFlags
                      -- GHC.liftIO $ GHC.throwIO $ GHC.mkSrcErr (unitBag $ GHC.mkPlainErrMsg dflags span err)
                      case GHC.lexTokenStream strSrcBuf startLoc flags of
                       GHC.POk _ ts  -> return ts
                       GHC.PFailed span err ->
                         do dflags <- GHC.getDynFlags
                            error "parse failed2"
        GHC.liftIO $ putStrLn $ "got tt:[" ++ show tt ++ "]"


        -- Tokens ------------------------------------------------------
        ts <- GHC.getTokenStream (GHC.ms_mod modSum)
        GHC.liftIO $ putStrLn $ "got ts"
        rts <- GHC.getRichTokenStream (GHC.ms_mod modSum)
        GHC.liftIO $ putStrLn $ "got rts"
        -- GHC.liftIO (putStrLn $ "tokens=" ++ (showRichTokenStream rts))
        -- GHC.liftIO (putStrLn $ "tokens=" ++ (show $ tokenLocs rts))
        -- GHC.liftIO (putStrLn $ "tokens=" ++ (show $ map (\(GHC.L _ tok,s) -> (tok,s)) rts)) 
        -- GHC.liftIO (putStrLn $ "tokens=" ++ (showToks rts))

        -- addSourceToTokens :: RealSrcLoc -> StringBuffer -> [Located Token] -> [(Located Token, String)]
        -- let tt = GHC.addSourceToTokens (GHC.mkRealSrcLoc (GHC.mkFastString "f") 1 1) (GHC.stringToStringBuffer "hiding (a,b)") []
        -- GHC.liftIO (putStrLn $ "new tokens=" ++ (showToks tt))


        -- GHC.liftIO (putStrLn $ "ghcSrcLocs=" ++ (show $ ghcSrcLocs ps))
        -- GHC.liftIO (putStrLn $ "srcLocs=" ++ (show $ srcLocs ps))

        -- GHC.liftIO (putStrLn $ "locToExp=" ++ (showPpr $ locToExp (4,12) (4,16) rts ps))
        -- GHC.liftIO (putStrLn $ "locToExp=" ++ (SYB.showData SYB.Parser 0 $ locToExp (4,12) (4,16) rts ps))
        -- GHC.liftIO (putStrLn $ "locToExp1=" ++ (SYB.showData SYB.Parser 0 $ locToExp (4,8) (4,43) rts ps))
        -- GHC.liftIO (putStrLn $ "locToExp2=" ++ (SYB.showData SYB.Parser 0 $ locToExp (4,8) (4,40) rts ps))


        -- Inscopes ----------------------------------------------------
        -- GHC.liftIO (putStrLn $ "\ninscopes(showData)=" ++ (SYB.showData SYB.Parser 0 $ inscopes))
        -- names <- GHC.parseName "G.mkT"
        -- GHC.liftIO (putStrLn $ "\nparseName=" ++ (showGhc $ names))


        -- ParsedSource -----------------------------------------------
        -- GHC.liftIO (putStrLn $ "parsedSource(Ppr)=" ++ (showGhc $ GHC.pm_parsed_source p))
        -- GHC.liftIO (putStrLn $ "\nparsedSource(showData)=" ++ (SYB.showData SYB.Parser 0 $ GHC.pm_parsed_source p))

        -- RenamedSource -----------------------------------------------
        GHC.liftIO $ putStrLn $ "about to show renamedSource"

        GHC.liftIO (putStrLn $ "renamedSource(Ppr)=" ++ (showGhc $ GHC.tm_renamed_source t))
        GHC.liftIO (putStrLn $ "\nrenamedSource(showData)=" ++ (SYB.showData SYB.Renamer 0 $ GHC.tm_renamed_source t))

        -- GHC.liftIO (putStrLn $ "typeCheckedSource=" ++ (showGhc $ GHC.tm_typechecked_source t))
        -- GHC.liftIO (putStrLn $ "typeCheckedSource=" ++ (SYB.showData SYB.TypeChecker 0 $ GHC.tm_typechecked_source t))

        -- ModuleInfo ----------------------------------------------------------------
        -- GHC.liftIO (putStrLn $ "moduleInfo.TyThings=" ++ (SYB.showData SYB.Parser 0 $ GHC.modInfoTyThings $ GHC.tm_checked_module_info t))
        -- GHC.liftIO (putStrLn $ "moduleInfo.TyThings=" ++ (showGhc $ GHC.modInfoTyThings $ GHC.tm_checked_module_info t))
        -- GHC.liftIO (putStrLn $ "moduleInfo.TopLevelScope=" ++ (showGhc $ GHC.modInfoTopLevelScope $ GHC.tm_checked_module_info t))


        -- Investigating TypeCheckedModule, in t
        --GHC.liftIO (putStrLn $ "TypecheckedModule : tm_renamed_source(Ppr)=" ++ (showGhc $ GHC.tm_renamed_source t))
        --GHC.liftIO (putStrLn $ "TypecheckedModule : tm_renamed_source(showData)=" ++ (SYB.showData SYB.Parser 0 $ GHC.tm_renamed_source t))

        -- GHC.liftIO (putStrLn $ "TypecheckedModule : tm_typechecked_source(Ppr)=" ++ (showGhc $ GHC.tm_typechecked_source t))
        -- GHC.liftIO (putStrLn $ "TypecheckedModule : tm_typechecked_source(showData)=" ++ (SYB.showData SYB.Parser 0 $ GHC.tm_typechecked_source t))


        -- Core module -------------------------------------------------
        -- GHC.liftIO (putStrLn $ "TypecheckedModuleCoreModule : cm_binds(showData)=" ++ (SYB.showData SYB.TypeChecker 0 $ GHC.mg_binds c))

        -- GHC.liftIO (putStrLn $ "TypecheckedModuleCoreModule : cm_binds(showData)=" ++ (SYB.showData SYB.TypeChecker 0 $ GHC.exprsFreeVars $ getBinds $ GHC.mg_binds c))
        -- GHC.liftIO (putStrLn $ "TypecheckedModuleCoreModule : exprFreeVars cm_binds(showData)=" ++ (showGhc $ GHC.exprsFreeVars $ getBinds $ GHC.mg_binds c))
        -- GHC.liftIO (putStrLn $ "TypecheckedModuleCoreModule : exprFreeIds cm_binds(showPpr)=" ++ (showGhc $ map GHC.exprFreeIds $ getBinds $ GHC.mg_binds c))

        -- GHC.liftIO (putStrLn $ "TypecheckedModuleCoreModule : bindFreeVars cm_binds(showPpr)=" ++ (showGhc $ map GHC.bindFreeVars $ GHC.mg_binds c))


        return ()

-- ---------------------------------------------------------------------
-- Copied from the GHC source, for debugging

getModuleSourceAndFlags :: GHC.GhcMonad m => GHC.Module -> m (String, GHC.StringBuffer, GHC.DynFlags)
getModuleSourceAndFlags mod = do
  m <- GHC.getModSummary (GHC.moduleName mod)
  case GHC.ml_hs_file $ GHC.ms_location m of
    Nothing -> do dflags <- GHC.getDynFlags
                  -- liftIO $ GHC.throwIO $ GHC.mkApiErr dflags (text "No source available for module " <+> GHC.ppr mod)
                  error $ ("No source available for module " ++ showGhc mod)
    Just sourceFile -> do
        source <- GHC.liftIO $ GHC.hGetStringBuffer sourceFile
        return (sourceFile, source, GHC.ms_hspp_opts m)

-- return our temporary directory within tmp_dir, creating one if we
-- don't have one yet
getTempDir :: GHC.DynFlags -> IO FilePath
getTempDir dflags
  = do let ref = GHC.dirsToClean dflags
           tmp_dir = GHC.tmpDir dflags
       mapping <- readIORef ref
       case Map.lookup tmp_dir mapping of
           Nothing -> error "should already be a tmpDir"
           Just d -> return d



-- ---------------------------------------------------------------------

sbufToString :: GHC.StringBuffer -> String
sbufToString sb@(GHC.StringBuffer buf len cur) = GHC.lexemeToString sb len

-- ---------------------------------------------------------------------

getSuffix :: FilePath -> String
getSuffix fname = reverse $ fst $ break (== '.') $ reverse fname


-- | A GHC preprocessed file has the following comments at the top
-- # 1 "./test/testdata/BCpp.hs"
-- # 1 "<command-line>"
-- # 1 "./test/testdata/BCpp.hs"
-- This function reads the first line of the file and returns the
-- string in it.
-- NOTE: no error checking, will blow up if it fails
getOriginalFile :: FilePath -> IO (FilePath,FilePath)
getOriginalFile fname = do
  fcontents <- readFile fname
  let firstLine = head $ lines fcontents
  let (_,originalFname) = break (== '"') firstLine
  return $ (tail $ init $ originalFname,fname)

-- ---------------------------------------------------------------------



-- processVarUniques :: (SYB.Data a) => a -> IO a
processVarUniques t = SYB.everywhereMStaged SYB.TypeChecker (SYB.mkM showUnique) t
    where
        showUnique (var :: Var)
           = do GHC.liftIO $ putStrLn (showGhc (varUnique var))
                return var
        showUnique x = return x


tokenLocs toks = map (\(GHC.L l _, s) -> (l,s)) toks

getBinds :: [GHC.CoreBind] -> [GHC.CoreExpr]
getBinds xs = map (\(_,x) -> x) $ concatMap getBind xs
  where
    getBind (GHC.NonRec b e) = [(b,e)]
    getBind (GHC.Rec bs) = bs

{-
instance (Show GHC.TyThing) where
  show (GHC.AnId anId) = "(AnId " ++ (show anId) ++ ")"
  show _               = "(Another TyThing)"
-}
-- instance (Show GHC.Name) where

convertSource ps =1
  ps

ifToCase :: GHC.HsExpr GHC.RdrName -> GHC.HsExpr GHC.RdrName
--  HsIf (Maybe (SyntaxExpr id)) (LHsExpr id) (LHsExpr id) (LHsExpr id)
ifToCase (GHC.HsIf _se e1 e2 e3)
  = GHC.HsCase e1 (GHC.MatchGroup
                   [
                     (GHC.noLoc $ GHC.Match
                      [
                        GHC.noLoc $ GHC.ConPatIn (GHC.noLoc $ mkRdrUnqual $ mkVarOcc "True") (GHC.PrefixCon [])
                      ]
                      Nothing
                       ((GHC.GRHSs
                         [
                           GHC.noLoc $ GHC.GRHS [] e2
                         ] GHC.EmptyLocalBinds))
                      )
                   , (GHC.noLoc $ GHC.Match
                      [
                        GHC.noLoc $ GHC.ConPatIn (GHC.noLoc $ mkRdrUnqual $ mkVarOcc "False") (GHC.PrefixCon [])
                      ]
                      Nothing
                       ((GHC.GRHSs
                         [
                           GHC.noLoc $ GHC.GRHS [] e3
                         ] GHC.EmptyLocalBinds))
                      )
                   ] undefined)
ifToCase x                          = x




-- -----------------------------------------------------------------------------------------
-- From http://hpaste.org/65775
{-
   1. install first: ghc-paths, ghc-syb-utils
   2. make a file Test1.hs in this dir with what you want to parse/transform
   3 .run with: ghci -package ghc
-}

-- module Main where


-- main = example

example :: IO ()
example =
   GHC.runGhc (Just libdir) $ do
        dflags <- GHC.getSessionDynFlags
        let dflags' = foldl GHC.xopt_set dflags
                            [GHC.Opt_Cpp, GHC.Opt_ImplicitPrelude, GHC.Opt_MagicHash]
        _ <- GHC.setSessionDynFlags dflags'
        -- target <- GHC.guessTarget (targetMod ++ ".hs") Nothing
        target <- GHC.guessTarget targetFile Nothing
        GHC.setTargets [target]
        _ <- GHC.load GHC.LoadAllTargets
        modSum <- GHC.getModSummary $ GHC.mkModuleName targetMod
        p' <- GHC.parseModule modSum
        p <- GHC.typecheckModule p'
        let p' = processParsedMod shortenLists p
        -- GHC.liftIO (putStrLn . showParsedModule $ p)
        -- GHC.liftIO (putStrLn . showParsedModule $ p')
        GHC.liftIO (putStrLn $ showGhc $ GHC.tm_typechecked_source p')

showParsedModule p = SYB.showData SYB.TypeChecker 0 (GHC.tm_typechecked_source p)

processParsedMod f pm = pm { GHC.tm_typechecked_source = ps' }
  where
   ps  = GHC.tm_typechecked_source pm
   -- ps' = SYB.everythingStaged SYB.Parser (SYB.mkT f) -- does not work yet
   -- everythingStaged :: Stage -> (r -> r -> r) -> r -> GenericQ r -> GenericQ r

   ps' :: GHC.TypecheckedSource
   ps' = SYB.everywhere (SYB.mkT f) ps -- exception
   -- ps' = everywhereStaged SYB.Parser (SYB.mkT f) ps 


shortenLists :: GHC.HsExpr GHC.RdrName -> GHC.HsExpr GHC.RdrName
shortenLists (GHC.ExplicitList t exprs) = GHC.ExplicitList t []
shortenLists x                          = x

--
-- ---------------------------------------------------------------------
-- Test drive the RefactGhc monad transformer stack
{-
runR :: IO ()
runR = do
  let
   -- initialState = ReplState { repl_inputState = initInputState }
   initialState = RefSt 
	{ rsSettings = RefSet ["."]
        , rsUniqState = 1
        , rsTokenStream = [] -- :: [PosToken]
	, rsStreamModified = False -- :: Bool
	-- , rsPosition = (-1,-1) -- :: (Int,Int)
        }
  (_,s) <- runRefactGhc comp initialState
  -- putStrLn $ show (rsPosition s)
  return ()

comp :: RefactGhc ()
comp = do
    s <- get
    modInfo@((_, _, mod), toks) <- parseSourceFileGhc "./old/refactorer/B.hs"
    -- -- gs <- mapM GHC.showModule mod
    g <- GHC.getModuleGraph
    gs <- mapM GHC.showModule g
    GHC.liftIO (putStrLn $ "modulegraph=" ++ (show gs))
    -- put (s {rsPosition = (123,456)})
    return ()
-}

-- ---------------------------------------------------------------------
{-
module B where
foo x = if (odd x) then \"Odd\" else \"Even\"
foo' x
  = case (odd x) of {
      True -> \"Odd\"
      False -> \"Even\" }
main = do { putStrLn $ show $ foo 5 }
mary = [1, 2, 3]"
*Main> :load "/home/alanz/mysrc/github/alanz/HaRe/refactorer/AzGhcPlay.hs"
[1 of 1] Compiling Main             ( /home/alanz/mysrc/github/alanz/HaRe/refactorer/AzGhcPlay.hs, interpreted )
Ok, modules loaded: Main.
*Main> 
*Main> 
*Main> 
*Main> getStuff
"
    (L {refactorer/B.hs:1:1} 
     (HsModule 
      (Just 
       (L {refactorer/B.hs:1:8} {ModuleName: B})) 
      (Nothing) 
      [] 
      [
       (L {refactorer/B.hs:4:1-41} 
        (ValD 
         (FunBind 
          (L {refactorer/B.hs:4:1-3} 
           (Unqual {OccName: foo})) 
          (False) 
          (MatchGroup 
           [
            (L {refactorer/B.hs:4:1-41} 
             (Match 
              [
               (L {refactorer/B.hs:4:5} 
                (VarPat 
                 (Unqual {OccName: x})))] 
              (Nothing) 
              (GRHSs 
               [
                (L {refactorer/B.hs:4:9-41} 
                 (GRHS 
                  [] 
                  (L {refactorer/B.hs:4:9-41} 
                   (HsIf 
                    (Just 
                     (HsLit 
                      (HsString {FastString: \"noSyntaxExpr\"}))) 
                    (L {refactorer/B.hs:4:12-18} 
                     (HsPar 
                      (L {refactorer/B.hs:4:13-17} 
                       (HsApp 
                        (L {refactorer/B.hs:4:13-15} 
                         (HsVar 
                          (Unqual {OccName: odd}))) 
                        (L {refactorer/B.hs:4:17} 
                         (HsVar 
                          (Unqual {OccName: x}))))))) 
                    (L {refactorer/B.hs:4:25-29} 
                     (HsLit 
                      (HsString {FastString: \"Odd\"}))) 
                    (L {refactorer/B.hs:4:36-41} 
                     (HsLit 
                      (HsString {FastString: \"Even\"})))))))] 
               (EmptyLocalBinds))))] {!type placeholder here?!}) 
          (WpHole) {!NameSet placeholder here!} 
          (Nothing)))),
       (L {refactorer/B.hs:(6,1)-(8,17)} 
        (ValD 
         (FunBind 
          (L {refactorer/B.hs:6:1-4} 
           (Unqual {OccName: foo'})) 
          (False) 
          (MatchGroup 
           [
            (L {refactorer/B.hs:(6,1)-(8,17)} 
             (Match 
              [
               (L {refactorer/B.hs:6:6} 
                (VarPat 
                 (Unqual {OccName: x})))] 
              (Nothing) 
              (GRHSs 
               [
                (L {refactorer/B.hs:(6,10)-(8,17)} 
                 (GRHS 
                  [] 
                  (L {refactorer/B.hs:(6,10)-(8,17)} 
                   (HsCase 
                    (L {refactorer/B.hs:6:15-21} 
                     (HsPar 
                      (L {refactorer/B.hs:6:16-20} 
                       (HsApp 
                        (L {refactorer/B.hs:6:16-18} 
                         (HsVar 
                          (Unqual {OccName: odd}))) 
                        (L {refactorer/B.hs:6:20} 
                         (HsVar 
                          (Unqual {OccName: x}))))))) 
                    (MatchGroup 
                     [
                      (L {refactorer/B.hs:7:3-15} 
                       (Match 
                        [
                         (L {refactorer/B.hs:7:3-6} 
                          (ConPatIn 
                           (L {refactorer/B.hs:7:3-6} 
                            (Unqual {OccName: True})) 
                           (PrefixCon 
                            [])))] 
                        (Nothing) 
                        (GRHSs 
                         [
                          (L {refactorer/B.hs:7:11-15} 
                           (GRHS 
                            [] 
                            (L {refactorer/B.hs:7:11-15} 
                             (HsLit 
                              (HsString {FastString: \"Odd\"})))))] 
                         (EmptyLocalBinds)))),
                      (L {refactorer/B.hs:8:3-17} 
                       (Match 
                        [
                         (L {refactorer/B.hs:8:3-7} 
                          (ConPatIn 
                           (L {refactorer/B.hs:8:3-7} 
                            (Unqual {OccName: False})) 
                           (PrefixCon 
                            [])))] 
                        (Nothing) 
                        (GRHSs 
                         [
                          (L {refactorer/B.hs:8:12-17} 
                           (GRHS 
                            [] 
                            (L {refactorer/B.hs:8:12-17} 
                             (HsLit 
                              (HsString {FastString: \"Even\"})))))] 
                         (EmptyLocalBinds))))] {!type placeholder here?!})))))] 
               (EmptyLocalBinds))))] {!type placeholder here?!}) 
          (WpHole) {!NameSet placeholder here!} 
          (Nothing)))),
       (L {refactorer/B.hs:(10,1)-(11,25)} 
        (ValD 
         (FunBind 
          (L {refactorer/B.hs:10:1-4} 
           (Unqual {OccName: main})) 
          (False) 
          (MatchGroup 
           [
            (L {refactorer/B.hs:(10,1)-(11,25)} 
             (Match 
              [] 
              (Nothing) 
              (GRHSs 
               [
                (L {refactorer/B.hs:(10,8)-(11,25)} 
                 (GRHS 
                  [] 
                  (L {refactorer/B.hs:(10,8)-(11,25)} 
                   (HsDo 
                    (DoExpr) 
                    [
                     (L {refactorer/B.hs:11:3-25} 
                      (ExprStmt 
                       (L {refactorer/B.hs:11:3-25} 
                        (OpApp 
                         (L {refactorer/B.hs:11:3-17} 
                          (OpApp 
                           (L {refactorer/B.hs:11:3-10} 
                            (HsVar 
                             (Unqual {OccName: putStrLn}))) 
                           (L {refactorer/B.hs:11:12} 
                            (HsVar 
                             (Unqual {OccName: $}))) {!fixity placeholder here?!} 
                           (L {refactorer/B.hs:11:14-17} 
                            (HsVar 
                             (Unqual {OccName: show}))))) 
                         (L {refactorer/B.hs:11:19} 
                          (HsVar 
                           (Unqual {OccName: $}))) {!fixity placeholder here?!} 
                         (L {refactorer/B.hs:11:21-25} 
                          (HsApp 
                           (L {refactorer/B.hs:11:21-23} 
                            (HsVar 
                             (Unqual {OccName: foo}))) 
                           (L {refactorer/B.hs:11:25} 
                            (HsOverLit 
                             (OverLit 
                              (HsIntegral 
                               (5)) 
                              (*** Exception: noRebindableInfo
   -}

-- |Show a GHC API structure
showGhc :: (GHC.Outputable a) => a -> String
#if __GLASGOW_HASKELL__ > 704
showGhc x = GHC.showSDoc GHC.tracingDynFlags $ GHC.ppr x
#else
showGhc x = GHC.showSDoc                     $ GHC.ppr x
#endif
