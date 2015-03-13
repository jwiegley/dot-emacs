module Process ( outsideProcess
               , outsideProcess'
               , insideProcess
               , insideProcess'
               , ghcPkgDbPathLocation
               , externalGhcPkgDb
               ) where

import           HsenvMonad
import           Paths
import           Types

import           Util.IO            (Environment, readProcessWithExitCodeInEnv, which)

import           Data.Maybe         (fromMaybe)
import           System.Environment (getEnvironment)
import           System.Exit        (ExitCode(..))
import           System.FilePath    ((</>))
import           System.Process     (readProcessWithExitCode)

runProcess :: Maybe Environment -> FilePath -> [String] -> Maybe String -> Hsenv String
runProcess env prog args input = do
  case input of
    Nothing  -> return ()
    Just inp -> do
      trace "Using the following input:"
      indentMessages $ mapM_ trace $ lines inp

  let execProcess = case env of
         Nothing   -> readProcessWithExitCode prog args (fromMaybe "" input)
         Just env' -> readProcessWithExitCodeInEnv env' prog args input

  (exitCode, output, errors) <- liftIO execProcess

  debug $ case exitCode of
    ExitSuccess         -> "Process exited successfully"
    ExitFailure errCode -> "Process failed with exit code " ++ show errCode

  case output of
    "" -> trace "Empty process output"
    _  -> do
      trace "Process output:"
      indentMessages $ mapM_ trace $ lines output

  case errors of
    "" -> trace "Empty process error output"
    _  -> do
      trace "Process error output:"
      indentMessages $ mapM_ trace $ lines errors

  case exitCode of
    ExitSuccess         -> return output
    ExitFailure errCode -> throwError $ HsenvException $ prog ++ " process failed with status " ++ show errCode

-- run regular process, takes:
-- * program name, looks for it in $PATH,
-- * list of arguments
-- * maybe standard input
-- returns standard output
outsideProcess :: String -> [String] -> Maybe String -> Hsenv String
outsideProcess progName args input = do
  debug $ unwords $ ["Running outside process:", progName] ++ args
  indentMessages $ do
    trace $ unwords ["Looking for", progName, "in $PATH"]
    program <- liftIO $ which Nothing progName
    case program of
      Nothing -> throwError $ HsenvException $ unwords ["No", progName, "in $PATH"]
      Just programPath -> do
        trace $ unwords [progName, "->", programPath]
        runProcess Nothing programPath args input

outsideProcess' :: String -> [String] -> Hsenv String
outsideProcess' progName args = outsideProcess progName args Nothing

-- returns path to GHC (installed from tarball) builtin package database
externalGhcPkgDb :: Hsenv FilePath
externalGhcPkgDb = do
  trace "Checking where GHC (installed from tarball) keeps its package database"
  indentMessages $ do
    dirStructure <- hseDirStructure
    let ghcPkg = ghcDir dirStructure </> "bin" </> "ghc-pkg"
    trace $ unwords ["Running process:", ghcPkg, "list"]
    ghcPkgOutput <- indentMessages $ runProcess Nothing ghcPkg ["list"] Nothing
    debug "Trying to parse ghc-pkg's output"
    case lines ghcPkgOutput of
      []             -> throwError $ HsenvException "ghc-pkg returned empty output"
      lineWithPath:_ ->
          case lineWithPath of
            "" -> throwError $ HsenvException "ghc-pkg's first line of output is empty"
            _  -> do
              -- ghc-pkg ends pkg db path with trailing colon
              -- but only when not run from the terminal
              let path = init lineWithPath
              debug $ "Found: " ++ path
              return path

-- returns value of GHC_PACKAGE_PATH that should be used inside virtual environment
-- defined in this module, because insideProcess needs it
ghcPkgDbPathLocation :: Hsenv String
ghcPkgDbPathLocation = do
  trace "Determining value of GHC_PACKAGE_PATH to be used inside virtual environment"
  dirStructure <- hseDirStructure
  ghc <- asks ghcSource
  case ghc of
    System -> return $ ghcPackagePath dirStructure
    _      -> do
             externalGhcPkgDbPath <- indentMessages externalGhcPkgDb
             return $ ghcPackagePath dirStructure ++ ":" ++ externalGhcPkgDbPath

virtualEnvironment :: Hsenv Environment
virtualEnvironment = do
  debug "Calculating unix env dictionary used inside virtual environment"
  indentMessages $ do
    env <- liftIO getEnvironment
    ghcPkgDb <- ghcPkgDbPathLocation
    debug $ "$GHC_PACKAGE_PATH=" ++ ghcPkgDb
    pathVar <- insidePathVar
    debug $ "$PATH=" ++ pathVar
    let varToBeOverridden var = var `elem` ["GHC_PACKAGE_PATH", "PATH"]
        strippedEnv = filter (not . varToBeOverridden . fst) env
    return $ [("GHC_PACKAGE_PATH", ghcPkgDb), ("PATH", pathVar)] ++ strippedEnv

-- run process from inside the virtual environment, takes:
-- * program name, looks for it in (in order):
--    - cabal bin dir (e.g. .hsenv*/cabal/bin)
--    - ghc bin dir (e.g. .hsenv*/ghc/bin), only when using ghc from tarball
--    - $PATH
-- * list of arguments
-- * maybe standard input
-- returns standard output
-- process is run in altered environment (new $GHC_PACKAGE_PATH env var,
-- adjusted $PATH var)
insideProcess :: String -> [String] -> Maybe String -> Hsenv String
insideProcess = insideProcess' False

-- like insideProcess, but if skipGhcPkgPathVar is True, GHC_PACKAGE_PATH is not added
insideProcess' :: Bool -> String -> [String] -> Maybe String -> Hsenv String
insideProcess' skipGhcPkgPathVar progName args input = do
  debug $ unwords $ ["Running inside process:", progName] ++ args
  indentMessages $ do
    pathVar <- insidePathVar
    trace $ unwords ["Looking for", progName, "in", pathVar]
    program <- liftIO $ which (Just pathVar) progName
    case program of
      Nothing -> throwError $ HsenvException $ unwords ["No", progName, "in", pathVar]
      Just programPath -> do
        trace $ unwords [progName, "->", programPath]
        env <- virtualEnvironment
        let env' = if skipGhcPkgPathVar then
                       filter (\(k, _) -> k /= "GHC_PACKAGE_PATH") env
                   else
                       env
        runProcess (Just env') programPath args input
