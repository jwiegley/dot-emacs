module Paths ( hseDirStructure
             , cabalConfigLocation
             , dotDirName
             , constructDotDirName
             , insidePathVar
             , cachedCabalInstallPath
             ) where

import Data.List (intercalate)
import Distribution.Version (Version)
import System.Directory (getAppUserDataDirectory)
import System.FilePath ((</>))

import Util.IO (getEnvVar)
import Util.Cabal (prettyVersion)
import Types
import HsenvMonad

-- returns record containing paths to all important directories
-- inside virtual environment dir structure
hseDirStructure :: Hsenv DirStructure
hseDirStructure = do
  parentDir <- asks envParentDir
  dirName <- dotDirName
  let hsEnvLocation    = parentDir
      hsEnvDirLocation = hsEnvLocation </> dirName
      cabalDirLocation = hsEnvDirLocation </> "cabal"
      ghcDirLocation   = hsEnvDirLocation </> "ghc"
  return DirStructure { hsEnv          = hsEnvLocation
                      , hsEnvDir       = hsEnvDirLocation
                      , ghcPackagePath = hsEnvDirLocation </> "ghc_pkg_db"
                      , cabalDir       = cabalDirLocation
                      , cabalBinDir    = cabalDirLocation </> "bin"
                      , hsEnvBinDir    = hsEnvDirLocation </> "bin"
                      , ghcDir         = ghcDirLocation
                      , ghcBinDir      = ghcDirLocation </> "bin"
                      }

constructDotDirName :: Options -> String
constructDotDirName opts = maybe ".hsenv" (".hsenv_" ++) (hsEnvName opts)

-- directory name of hsEnvDir
dotDirName :: Hsenv String
dotDirName = do
  opts <- ask
  return $ constructDotDirName opts

-- returns location of cabal's config file inside virtual environment dir structure
cabalConfigLocation :: Hsenv FilePath
cabalConfigLocation = do
  dirStructure <- hseDirStructure
  return $ cabalDir dirStructure </> "config"

-- returns value of $PATH env variable to be used inside virtual environment
insidePathVar :: Hsenv String
insidePathVar = do
  oldPathVar <- liftIO $ getEnvVar "PATH"
  let oldPathVarSuffix = case oldPathVar of
                           Nothing -> ""
                           Just x  -> ':' : x
  dirStructure <- hseDirStructure
  ghc          <- asks ghcSource
  let extraPathElems = case ghc of
                         System -> [cabalBinDir dirStructure]
                         _      -> [cabalBinDir dirStructure, ghcBinDir dirStructure]
  return $ intercalate ":" extraPathElems ++ oldPathVarSuffix

-- returns path to ~/.hsenv dir
userHsenvDir :: Hsenv FilePath
userHsenvDir = liftIO $ getAppUserDataDirectory "hsenv"

-- returns path to ~/.hsenv/cache directory
userCacheDir :: Hsenv FilePath
userCacheDir = do
  baseDir <- userHsenvDir
  return $ baseDir </> "cache"

-- returns path to cached version of compiled binary for cabal-install
-- (depends on Cabal library version),
-- e.g. ~/.hsenv/cache/cabal-install/Cabal-0.14.0
cachedCabalInstallPath :: Version -> Hsenv FilePath
cachedCabalInstallPath cabalVersion = do
  cacheDir <- userCacheDir
  let cabInsCachePath = cacheDir </> "cabal-install"
  return $ cabInsCachePath </> "Cabal-" ++ prettyVersion cabalVersion
