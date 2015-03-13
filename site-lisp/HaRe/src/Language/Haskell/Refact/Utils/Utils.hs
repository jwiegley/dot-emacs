{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}

module Language.Haskell.Refact.Utils.Utils
       (
       -- * Managing the GHC / project environment
         getModuleGhc
       , parseSourceFileGhc
       , activateModule
       , getModuleDetails

       -- * The bits that do the work
       , runRefacSession
       , applyRefac
       , refactDone
       , ApplyRefacResult
       , RefacSource(..)

       , update
       , fileNameToModName
       , fileNameFromModSummary
       , getModuleName
       , clientModsAndFiles
       , serverModsAndFiles

       ) where

import Control.Monad.State
import Data.List
import Data.Maybe
import Language.Haskell.GhcMod
import Language.Haskell.Refact.Utils.GhcBugWorkArounds
import Language.Haskell.Refact.Utils.GhcModuleGraph
import Language.Haskell.Refact.Utils.GhcUtils
import Language.Haskell.Refact.Utils.GhcVersionSpecific
import Language.Haskell.Refact.Utils.LocUtils
import Language.Haskell.Refact.Utils.Monad
import Language.Haskell.Refact.Utils.MonadFunctions
import Language.Haskell.Refact.Utils.TypeSyn
import Language.Haskell.Refact.Utils.TypeUtils
import Language.Haskell.TokenUtils.DualTree
import Language.Haskell.TokenUtils.TokenUtils
import Language.Haskell.TokenUtils.Utils
import System.Directory
import System.FilePath.Posix

import qualified Digraph       as GHC
import qualified FastString    as GHC
import qualified GHC
import qualified Outputable    as GHC

import qualified Data.Generics as SYB
import qualified GHC.SYB.Utils as SYB

-- import Debug.Trace

-- ---------------------------------------------------------------------

-- | From file name to module name.
fileNameToModName :: FilePath -> RefactGhc GHC.ModuleName
fileNameToModName fileName = do
  mm <- getModuleMaybe fileName
  case mm of
    Nothing -> error $ "Can't find module name"
    Just ms ->  return $ GHC.moduleName $ GHC.ms_mod ms

-- ---------------------------------------------------------------------

getModuleMaybe :: FilePath -> RefactGhc (Maybe GHC.ModSummary)
getModuleMaybe fileName = do
  cfileName <- liftIO $ canonicalizePath fileName
  -- logm $ "getModuleMaybe for (fileName,cfileName):" ++ show (fileName,cfileName)

  graphs <- gets rsGraph
  currentTgt <- gets rsCurrentTarget
  logm $ "getModuleMaybe " ++ show fileName ++ ":" ++ show (length graphs,currentTgt)

  let cgraph = concatMap (\(_,cg) -> cg) graphs
  -- graph <- GHC.getModuleGraph
  -- cgraph <- liftIO $ canonicalizeGraph graph

  -- logm $ "getModuleMaybe: [mfn]=" ++ show (map (\(mfn,_ms) -> mfn) cgraph)

  let mm = filter (\(mfn,_ms) -> mfn == Just cfileName) cgraph
  -- logm $ "getModuleMaybe: mm=" ++ show mm

  case mm of
    [] -> return Nothing
    _ -> do
      let (_mfn,ms) = (ghead "getModuleMaybe" mm)
      -- activateModule (fromJust mfn,ms)
      return $ Just ms

-- ---------------------------------------------------------------------

-- | Extract the module name from the parsed source, if there is one
getModuleName :: GHC.ParsedSource -> Maybe (GHC.ModuleName,String)
getModuleName (GHC.L _ modn) =
  case (GHC.hsmodName modn) of
    Nothing -> Nothing
    Just (GHC.L _ modname) -> Just $ (modname,GHC.moduleNameString modname)

-- ---------------------------------------------------------------------

-- | Once the module graph has been loaded, load the given module into
-- the RefactGhc monad
-- TODO: relax the equality test, if the file is loaded via cabal it
-- may have a full filesystem path.
getModuleGhc ::
  FilePath -> RefactGhc ()
getModuleGhc targetFile = do
  -- TODO: consult cached store of multiple module graphs, one for
  --       each main file.
  mTarget <- identifyTargetModule targetFile
  case mTarget of
    Nothing -> return ()
    Just tm -> do
      void $ activateModule tm
      return ()

  mm <- getModuleMaybe targetFile
  case mm of
    Just ms -> getModuleDetails ms
    Nothing -> parseSourceFileGhc targetFile

-- ---------------------------------------------------------------------

identifyTargetModule :: FilePath -> RefactGhc (Maybe TargetModule)
identifyTargetModule targetFile = do
  currentDirectory <- liftIO getCurrentDirectory
  target1 <- liftIO $ canonicalizePath targetFile
  target2 <- liftIO $ canonicalizePath (combine currentDirectory targetFile)
  -- logm $ "identifyTargetModule:(targetFile,target1,target2)=" ++ show (targetFile,target1,target2)
  graphs <- gets rsModuleGraph

  -- logm $ "identifyTargetModule:graphs=" ++ show graphs

  let ff = catMaybes $ map (findInTarget target1 target2) graphs
  -- logm $ "identifyTargetModule:ff=" ++ show ff
  case ff of
    [] -> return Nothing
    ms -> return (Just (ghead ("identifyTargetModule:" ++ (show ms)) ms))

findInTarget :: FilePath -> FilePath -> ([FilePath],GHC.ModuleGraph) -> Maybe TargetModule
findInTarget f1 f2 (fps,graph) = r'
  where
    -- We also need to process the case where it is a main file for an exe.
    re :: Maybe TargetModule
    re = case fps of
      [x] -> re' -- single target, could be an exe
       where
         re' = case filter isMainModSummary graph of
           [] -> Nothing
           ms -> if x == f1 || x == f2 then Just (fps,ghead "findInTarget" ms)
                                      else Nothing
      _  -> Nothing
    isMainModSummary ms = (show $ GHC.ms_mod ms) == "Main"

    r = case filter (compModFiles f1 f2) graph of
          [] -> Nothing
          ms -> Just (fps,ghead "findInTarget.2" ms)
    compModFiles :: FilePath-> FilePath -> GHC.ModSummary -> Bool
    compModFiles fileName1 fileName2 ms =
      case GHC.ml_hs_file $ GHC.ms_location ms of
        Nothing -> False
        Just fn -> fn == fileName1 || fn == fileName2

    r' = listToMaybe $ catMaybes [r,re]

-- ---------------------------------------------------------------------

-- | In the existing GHC session, put the requested TypeCheckedModule
-- into the RefactGhc Monad, after ensuring that its originating
-- target is the currently loaded one

activateModule :: TargetModule -> RefactGhc GHC.ModSummary
activateModule (target, modSum) = do
  logm $ "activateModule:" ++ show (target,GHC.ms_mod modSum)
  newModSum <- ensureTargetLoaded (target,modSum)
  getModuleDetails newModSum
  return newModSum

-- ---------------------------------------------------------------------

-- | In the existing GHC session, put the requested TypeCheckedModule
-- into the RefactGhc monad

-- TODO: rename this function, it is not clear in a refactoring what
-- it does
getModuleDetails :: GHC.ModSummary -> RefactGhc ()
getModuleDetails modSum = do
      p <- GHC.parseModule modSum
      t <- GHC.typecheckModule p

      -- GHC.setContext [GHC.IIModule (GHC.moduleName $ GHC.ms_mod modSum)]
      setGhcContext modSum

      -- Use the workaround to get the tokens, the existing one does
      -- not return tokens for CPP processed files.
      -- tokens <- GHC.getRichTokenStream (GHC.ms_mod modSum)
      tokens <- getRichTokenStreamWA (GHC.ms_mod modSum)
      mtm <- gets rsModule
      case mtm of
        Just tm -> if ((rsStreamModified tm == False)
                      && ((GHC.mkFastString $ fileNameFromModSummary modSum) ==
                          (fileNameFromTok $ ghead "getModuleDetails" tokens)))
                     then return ()
                     else if rsStreamModified tm == False
                            then putParsedModule t tokens
                            else error $ "getModuleDetails: trying to load a module without finishing with active one."

        Nothing -> putParsedModule t tokens

      return ()

-- ---------------------------------------------------------------------

-- | Parse a single source file into a GHC session
parseSourceFileGhc :: FilePath -> RefactGhc ()
parseSourceFileGhc targetFile = do
     {-
      target <- GHC.guessTarget ("*" ++ targetFile) Nothing -- The *
                                     -- is to force interpretation, for inscopes
      GHC.setTargets [target]
      void $ GHC.load GHC.LoadAllTargets -- Loads and compiles, much as calling ghc --make
     -}
      -- logm $ "parseSourceFileGhc:about to loadModuleGraphGhc for" ++ (show targetFile)
      loadModuleGraphGhc (Just [targetFile])
      -- logm $ "parseSourceFileGhc:loadModuleGraphGhc done"

      mm <- getModuleMaybe targetFile
      case mm of
        Nothing -> error $ "HaRe:unexpected error parsing " ++ targetFile
        Just modSum -> getModuleDetails modSum

-- ---------------------------------------------------------------------

-- | The result of a refactoring is the file, a flag as to whether it
-- was modified, the updated token stream, and the updated AST
-- type ApplyRefacResult = ((FilePath, Bool), ([Ppr],[PosToken], GHC.RenamedSource))
type ApplyRefacResult = ((FilePath, Bool), ([Line PosToken],[PosToken], GHC.RenamedSource))


-- | Manage a whole refactor session. Initialise the monad, load the
-- whole project if required, and then apply the individual
-- refactorings, and write out the resulting files.
--
-- It is intended that this forms the umbrella function, in which
-- applyRefac is called
--
runRefacSession ::
       RefactSettings
    -> Cradle                       -- ^ Identifies the surrounding
                                    -- project
    -> RefactGhc [ApplyRefacResult] -- ^ The computation doing the
                                    -- refactoring. Normally created
                                    -- via 'applyRefac'
    -> IO [FilePath]
runRefacSession settings cradle comp = do
  let
   initialState = RefSt
        { rsSettings = settings
        , rsUniqState = 1
        , rsFlags = RefFlags False
        , rsStorage = StorageNone
        , rsGraph = []
        , rsModuleGraph = []
        , rsCurrentTarget = Nothing
        , rsModule = Nothing
        }

  (refactoredMods,_s) <- runRefactGhc (initGhcSession cradle (rsetImportPaths settings) >>
                                       comp) initialState

  let verbosity = rsetVerboseLevel (rsSettings initialState)
  writeRefactoredFiles verbosity refactoredMods
  return $ modifiedFiles refactoredMods

-- ---------------------------------------------------------------------

data RefacSource = RSFile FilePath
                 | RSMod GHC.ModSummary
                 | RSAlreadyLoaded

-- TODO: the module should be stored in the state, and returned if it
-- has been modified in a prior refactoring, instead of being parsed
-- afresh each time.

-- | Apply a refactoring (or part of a refactoring) to a single module
applyRefac
    :: RefactGhc a       -- ^ The refactoring
    -> RefacSource        -- ^ where to get the module and toks
    -> RefactGhc (ApplyRefacResult,a)

applyRefac refac source = do

    -- TODO: currently a temporary, poor man's surrounding state
    -- management: store state now, set it to fresh, run refac, then
    -- restore the state. Fix this to store the modules in some kind of cache.

    fileName <- case source of
         RSFile fname    -> do getModuleGhc fname
                               return fname
         RSMod  ms       -> do getModuleGhc $ fileNameFromModSummary ms
                               return $ fileNameFromModSummary ms
         RSAlreadyLoaded -> do mfn <- getRefactFileName
                               case mfn of
                                 Just fname -> return fname
                                 Nothing -> error "applyRefac RSAlreadyLoaded: nothing loaded"

    res <- refac  -- Run the refactoring, updating the state as required

    mod'   <- getRefactRenamed
    -- toks'  <- fetchToksFinal
    let toks' = []
    -- pprVal <- fetchPprFinal
    linesVal <- fetchLinesFinal
    m      <- getRefactStreamModified

    -- Clear the refactoring state
    clearParsedModule

    return (((fileName,m),(linesVal,toks', mod')),res)


-- ---------------------------------------------------------------------

-- |Returns True if any of the results has its modified flag set
refactDone :: [ApplyRefacResult] -> Bool
refactDone rs = any (\((_,d),_) -> d) rs

-- ---------------------------------------------------------------------


modifiedFiles :: [ApplyRefacResult] -> [String]
modifiedFiles refactResult = map (\((s,_),_) -> s)
                           $ filter (\((_,b),_) -> b) refactResult

-- ---------------------------------------------------------------------

fileNameFromModSummary :: GHC.ModSummary -> FilePath
fileNameFromModSummary modSummary = fileName
  where
    -- TODO: what if we are loading a compiled only client and do not
    -- have the original source?
    Just fileName = GHC.ml_hs_file (GHC.ms_location modSummary)

-- ---------------------------------------------------------------------

class (SYB.Data t, SYB.Data t1) => Update t t1 where

  -- | Update the occurrence of one syntax phrase in a given scope by
  -- another syntax phrase of the same type
  update::  t     -- ^ The syntax phrase to be updated.
         -> t     -- ^ The new syntax phrase.
         -> t1    -- ^ The contex where the old syntax phrase occurs.
         -> RefactGhc t1  -- ^ The result.

instance (SYB.Data t, GHC.OutputableBndr n, SYB.Data n) => Update (GHC.Located (GHC.HsExpr n)) t where
    update oldExp newExp t
           = everywhereMStaged SYB.Parser (SYB.mkM inExp) t
       where
        inExp (e::GHC.Located (GHC.HsExpr n))
          | sameOccurrence e oldExp
               = do
                    -- drawTokenTree "update Located HsExpr starting" -- ++AZ++
                    _ <- updateToks oldExp newExp prettyprint False
                    -- drawTokenTree "update Located HsExpr done" -- ++AZ++

                -- error "update: updated tokens" -- ++AZ++ debug
                    -- TODO: make sure to call syncAST
                    return newExp
          | otherwise = return e

instance (SYB.Data t, GHC.OutputableBndr n, SYB.Data n) => Update (GHC.LPat n) t where
    update oldPat newPat t
           = everywhereMStaged SYB.Parser (SYB.mkM inPat) t
        where
          inPat (p::GHC.LPat n)
            | sameOccurrence p oldPat
                = do
                     _ <- updateToks oldPat newPat prettyprint False
                     -- TODO: make sure to call syncAST
                     return newPat
            | otherwise = return p

instance (SYB.Data t, GHC.OutputableBndr n, SYB.Data n) => Update (GHC.LHsType n) t where
     update oldTy newTy t
           = everywhereMStaged SYB.Parser (SYB.mkM inTyp) t
        where
          inTyp (t'::GHC.LHsType n)
            | sameOccurrence t' oldTy
                = do
                     _ <- updateToks oldTy newTy prettyprint False
                     -- TODO: make sure to call syncAST
                     return newTy
            | otherwise = return t'

instance (SYB.Data t, GHC.OutputableBndr n1, GHC.OutputableBndr n2, SYB.Data n1, SYB.Data n2) => Update (GHC.LHsBindLR n1 n2) t where
       update oldBind newBind t
             = everywhereMStaged SYB.Parser (SYB.mkM inBind) t
          where
            inBind (t'::GHC.LHsBindLR n1 n2)
              | sameOccurrence t' oldBind
                  = do
                       _ <- updateToks oldBind newBind prettyprint False
                       -- TODO: make sure to call syncAST
                       return newBind
              | otherwise = return t'


-- ---------------------------------------------------------------------

-- | Write refactored program source to files.
writeRefactoredFiles ::
  VerboseLevel -> [ApplyRefacResult] -> IO ()
writeRefactoredFiles verbosity files
  = do let filesModified = filter (\((_f,m),_) -> m == modified) files

       -- TODO: restore the history function
       -- ++AZ++ PFE0.addToHistory isSubRefactor (map (fst.fst) filesModified)
       sequence_ (map modifyFile filesModified)
       -- mapM_ writeTestDataForFile files   -- This should be removed for the release version.

     where
       modifyFile ((fileName,_),(finalLines,ts,renamed)) = do
           -- let source = concatMap (snd.snd) ts

           let ts' = bypassGHCBug7351 ts
           -- let source = GHC.showRichTokenStream ts'

           -- let source = renderPpr ppr
           let source = renderLines finalLines

           -- (Julien personnal remark) seq forces the evaluation of
           -- its first argument and returns its second argument. It
           -- is unclear for me why (length source) evaluation is
           -- forced.
           let (baseFileName,ext) = splitExtension fileName
           seq (length source) (writeFile (baseFileName ++ ".refactored" ++ ext) source)

           when (verbosity == Debug) $
             do
               writeFile (fileName ++ ".tokens") (showToks ts')
               writeFile (fileName ++ ".renamed_out") (showGhc renamed)
               writeFile (fileName ++ ".AST_out") $ ((showGhc renamed) ++
                      "\n\n----------------------\n\n" ++
                      (SYB.showData SYB.Renamer 0 renamed))

-- ---------------------------------------------------------------------

-- | Return the client modules and file names. The client modules of
-- module, say m, are those modules which directly or indirectly
-- import module m.

-- TODO: deal with an anonymous main module, by taking Maybe GHC.ModuleName
clientModsAndFiles
  :: GHC.ModuleName -> RefactGhc [([FilePath],GHC.ModSummary)]
clientModsAndFiles m = do
  modsum <- GHC.getModSummary m

  -- ms' <- GHC.getModuleGraph
  ms' <- gets rsModuleGraph
  -- target <- gets rsCurrentTarget

  let getClients ms = clientMods
        where
          mg = getModulesAsGraph False ms Nothing
          rg = GHC.transposeG mg
          {-
          modNode = gfromJust ("clientModsAndFiles:" ++ (showGhc (GHC.ms_mod modsum,target,mg))) 
                  $ find (\(msum',_,_) -> mycomp msum' modsum) (GHC.verticesG rg)
          clientMods = filter (\msum' -> not (mycomp msum' modsum))
                     $ map summaryNodeSummary $ GHC.reachableG rg modNode
          -}
          maybeModNode = find (\(msum',_,_) -> mycomp msum' modsum) (GHC.verticesG rg)
          clientMods = case maybeModNode of
                         Nothing -> []
                         Just modNode ->
                           filter (\msum' -> not (mycomp msum' modsum))
                           $ map summaryNodeSummary $ GHC.reachableG rg modNode

  let clients = concatMap (\(f,mg) -> zip (repeat f) (getClients mg)) ms'
  -- Need to strip out duplicates, based on the snd of the tuple
      clients' = nubBy cc clients
      cc (_,mg1) (_,mg2)
        = if (show $ GHC.ms_mod mg1) == "Main" || (show $ GHC.ms_mod mg2) == "Main" 
            then False
            else mycomp mg1 mg2

  logm $ "clientModsAndFiles:clients=" ++ show clients
  logm $ "clientModsAndFiles:clients'=" ++ show clients'
  return clients'

-- TODO : find decent name and place for this.
mycomp :: GHC.ModSummary -> GHC.ModSummary -> Bool
mycomp ms1 ms2 = (GHC.ms_mod ms1) == (GHC.ms_mod ms2)


-- ---------------------------------------------------------------------

-- | Return the server module and file names. The server modules of
-- module, say m, are those modules which are directly or indirectly
-- imported by module m. This can only be called in a live GHC session
-- TODO: make sure this works with multiple targets. Is that needed? No?
serverModsAndFiles
  :: GHC.GhcMonad m => GHC.ModuleName -> m [GHC.ModSummary]
serverModsAndFiles m = do
  ms <- GHC.getModuleGraph
  modsum <- GHC.getModSummary m
  let mg = getModulesAsGraph False ms Nothing
      modNode = gfromJust "serverModsAndFiles" $ find (\(msum',_,_) -> mycomp msum' modsum) (GHC.verticesG mg)
      serverMods = filter (\msum' -> not (mycomp msum' modsum))
                 $ map summaryNodeSummary $ GHC.reachableG mg modNode

  return serverMods

-- ---------------------------------------------------------------------

instance (Show GHC.ModuleName) where
  show = GHC.moduleNameString

-- ---------------------------------------------------------------------
