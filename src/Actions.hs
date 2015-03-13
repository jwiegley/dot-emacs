module Actions ( cabalUpdate
               , installCabalConfig
               , installCabalWrapper
               , installActivateScript
               , installSimpleWrappers
               , installProgSymlinks
               , symlinkToSkeleton
               , copyBaseSystem
               , initGhcDb
               , installGhc
               , createDirStructure
               , bootstrapCabal
               , initDotHsenvDir
               ) where

import Control.Monad
import System.Directory
import System.FilePath ((</>))
import System.Info (arch, os)
import System.Posix hiding (createDirectory, version)
import Distribution.Version (Version (..))
import Distribution.Package (PackageName(..))
import Safe (lastMay)
import Data.List (intercalate)
import Data.Maybe (fromMaybe, isJust)

import Network.Http.Client
import qualified Data.ByteString.Char8 as C8
import qualified System.IO.Streams as S

import HsenvMonad
import HsenvMonadUtils
import Types
import Paths
import PackageManagement
import Process
import Util.Template (substs)
import Util.IO (makeExecutable)
import Skeletons
import CabalBootstrap (bootstrapCabal)

-- update cabal package info inside Virtual Haskell Environment
cabalUpdate :: Hsenv ()
cabalUpdate = do
  noSharingFlag <- asks noSharing
  if noSharingFlag then do
    debug "Sharing user-wide ~/.cabal/packages disabled"
    cabalUpdate'
   else do
    debug "Sharing user-wide ~/.cabal/packages enabled, checking if data is already downloaded"
    cabalInstallDir <- liftIO $ getAppUserDataDirectory "cabal"
    let hackageData = foldl (</>) cabalInstallDir [ "packages"
                                                  , "hackage.haskell.org"
                                                  , "00-index.tar"
                                                  ]
    dataExists <- liftIO $ doesFileExist hackageData
    if dataExists then do
      info "Skipping 'cabal update' step, Hackage download cache already downloaded"
      info "  to ~/.cabal/packages/. You can update it manually with 'cabal update'"
      info "  (from inside or outside the virtual environment)."
     else do
      debug "No user-wide Hackage cache data downloaded"
      cabalUpdate'
      where cabalUpdate' = do
              cabalConfig <- cabalConfigLocation
              info "Updating cabal package database inside Virtual Haskell Environment."
              _ <- indentMessages $ insideProcess "cabal" ["--config-file=" ++ cabalConfig, "update"] Nothing
              return ()


-- install cabal wrapper (in bin/ directory) inside virtual environment dir structure
installCabalWrapper :: Hsenv ()
installCabalWrapper = do
  cabalConfig  <- cabalConfigLocation
  dirStructure <- hseDirStructure
  hsEnvName'   <- asks hsEnvName
  let cabalWrapper = hsEnvBinDir dirStructure </> "cabal"
  info $ concat [ "Installing cabal wrapper using "
                , cabalConfig
                , " at "
                , cabalWrapper
                ]
  let cabalWrapperContents = substs [ ("<CABAL_CONFIG>", cabalConfig)
                                    , ("<HSENV_NAME>", fromMaybe "" hsEnvName')] cabalWrapperSkel
  indentMessages $ do
    trace "cabal wrapper contents:"
    indentMessages $ mapM_ trace $ lines cabalWrapperContents
  liftIO $ writeFile cabalWrapper cabalWrapperContents
  liftIO $ makeExecutable cabalWrapper

installActivateScriptSupportFiles :: Hsenv ()
installActivateScriptSupportFiles = do
  debug "installing supporting files"
  dirStructure <- hseDirStructure
  ghc          <- asks ghcSource
  indentMessages $ do
    let pathVarPrependixLocation = hsEnvDir dirStructure </> "path_var_prependix"
        pathVarElems =
            case ghc of
              System -> [hsEnvBinDir dirStructure, cabalBinDir dirStructure]
              _      -> [ hsEnvBinDir dirStructure
                        , cabalBinDir dirStructure
                        , ghcBinDir dirStructure
                        ]
        pathVarPrependix = intercalate ":" pathVarElems
    debug $ "installing path_var_prependix file to " ++ pathVarPrependixLocation
    indentMessages $ trace $ "path_var_prependix contents: " ++ pathVarPrependix
    liftIO $ writeFile pathVarPrependixLocation pathVarPrependix
    ghcPkgDbPath <- indentMessages ghcPkgDbPathLocation
    let ghcPackagePathVarLocation = hsEnvDir dirStructure </> "ghc_package_path_var"
        ghcPackagePathVar         = ghcPkgDbPath
    debug $ "installing ghc_package_path_var file to " ++ ghcPackagePathVarLocation
    indentMessages $ trace $ "path_var_prependix contents: " ++ ghcPackagePathVar
    liftIO $ writeFile ghcPackagePathVarLocation ghcPackagePathVar

-- install activate script (in bin/ directory) inside virtual environment dir structure
installActivateScript :: Hsenv ()
installActivateScript = do
  info "Installing activate script"
  hsEnvName'   <- asks hsEnvName
  noModifyPS1  <- asks noPS1
  dirStructure <- hseDirStructure
  ghcPkgDbPath <- indentMessages ghcPkgDbPathLocation
  let activateScript = hsEnvBinDir dirStructure </> "activate"
  indentMessages $ debug $ "using location: " ++ activateScript
  let activateScriptContents =
          substs [ ("<HSENV_NAME>", fromMaybe "" hsEnvName')
                 , ("<HSENV_DIR>", hsEnvDir dirStructure)
                 , ("<HSENV>", hsEnv dirStructure)
                 , ("<GHC_PACKAGE_PATH>", ghcPkgDbPath)
                 , ("<HSENV_BIN_DIR>", hsEnvBinDir dirStructure)
                 , ("<CABAL_BIN_DIR>", cabalBinDir dirStructure)
                 , ("<GHC_BIN_DIR>", ghcBinDir dirStructure)
                 , ("<MODIFY_PS1>", if noModifyPS1 then "false" else "true")
                 ] activateSkel
  indentMessages $ do
    trace "activate script contents:"
    indentMessages $ mapM_ trace $ lines activateScriptContents
  liftIO $ writeFile activateScript activateScriptContents
  indentMessages installActivateScriptSupportFiles

-- install cabal's config file (in cabal/ directory) inside virtual environment dir structure
installCabalConfig :: Hsenv ()
installCabalConfig = do
  cabalConfig  <- cabalConfigLocation
  dirStructure <- hseDirStructure
  noSharingFlag  <- asks noSharing
  hackageCache <- indentMessages $
      if noSharingFlag then do
          info "Using private Hackage download cache directory"
          return $ cabalDir dirStructure </> "packages"
      else do
          info "Using user-wide (~/.cabal/packages) Hackage download cache directory"
          cabalInstallDir <- liftIO $ getAppUserDataDirectory "cabal"
          return $ cabalInstallDir </> "packages"
  info $ "Installing cabal config at " ++ cabalConfig
  let cabalConfigContents = substs [ ("<GHC_PACKAGE_PATH>", ghcPackagePath dirStructure)
                                   , ("<CABAL_DIR>", cabalDir dirStructure)
                                   , ("<HACKAGE_CACHE>", hackageCache)
                                   ] cabalConfigSkel
  indentMessages $ do
    trace "cabal config contents:"
    indentMessages $ mapM_ trace $ lines cabalConfigContents
  liftIO $ writeFile cabalConfig cabalConfigContents

installSimpleWrappers :: Hsenv ()
installSimpleWrappers = mapM_ installSimpleWrapper simpleWrappers

installSimpleWrapper :: (String, String) -> Hsenv ()
installSimpleWrapper (targetFilename, skeleton) = do
    ghcPkgDbPath <- indentMessages ghcPkgDbPathLocation
    dirStructure <- hseDirStructure
    let ghcWrapperContents =
            substs [("<GHC_PACKAGE_PATH>", ghcPkgDbPath)] skeleton
        ghcWrapper = hsEnvBinDir dirStructure </> targetFilename
    liftIO $ writeFile ghcWrapper ghcWrapperContents
    liftIO $ makeExecutable ghcWrapper

installProgSymlinks :: Hsenv ()
installProgSymlinks = mapM_ installSymlink extraProgs

extraProgs :: [String]
extraProgs = [ "alex"
             , "ar"
             , "c2hs"
             , "cpphs"
             , "ffihugs"
             , "gcc"
             , "greencard"
             , "haddock"
             , "happy"
             , "hmake"
             , "hpc"
             , "hsc2hs"
             , "hscolour"
             , "hugs"
             , "jhc"
             , "ld"
             , "lhc"
             , "lhc-pkg"
             , "nhc98"
             , "pkg-config"
             , "ranlib"
             , "strip"
             , "tar"
             , "uhc"
             ]

installSymlink :: String -> Hsenv ()
installSymlink prog = do
    dirStructure <- hseDirStructure
    ghcSourceOpt <- asks ghcSource
    mPrivateLoc <- case ghcSourceOpt of
        System -> return Nothing
        _      -> liftIO $ findExecutable $ ghcDir dirStructure </> "bin" </> prog
    mSystemLoc <- liftIO $ findExecutable prog
    let mProgLoc = mPrivateLoc `mplus` mSystemLoc
    when (isJust mProgLoc) $ do
        let Just progLoc = mProgLoc
        liftIO $ createSymbolicLink progLoc $ hsEnvBinDir dirStructure </> prog

-- | Install a symbolic link to a skeleton script in hsenv's bin directory
symlinkToSkeleton :: String -- ^ Name of skeleton
                  -> String -- ^ Name of link
                  -> Hsenv ()
symlinkToSkeleton skel link = do
    dirStructure <- hseDirStructure
    let prependBinDir = (hsEnvBinDir dirStructure </>)
    liftIO $ createSymbolicLink (prependBinDir skel) (prependBinDir link)

createDirStructure :: Hsenv ()
createDirStructure = do
  dirStructure <- hseDirStructure
  info "Creating Virtual Haskell directory structure"
  indentMessages $ do
    debug $ "hsenv directory: " ++ hsEnvDir dirStructure
    liftIO $ createDirectory $ hsEnvDir dirStructure
    debug $ "cabal directory: " ++ cabalDir dirStructure
    liftIO $ createDirectory $ cabalDir dirStructure
    debug $ "hsenv bin directory: " ++ hsEnvBinDir dirStructure
    liftIO $ createDirectory $ hsEnvBinDir dirStructure

-- initialize private GHC package database inside virtual environment
initGhcDb :: Hsenv ()
initGhcDb = do
  dirStructure <- hseDirStructure
  info $ "Initializing GHC Package database at " ++ ghcPackagePath dirStructure
  out <- indentMessages $ insideGhcPkg ["--version"] Nothing
  case lastMay $ words out of
    Nothing            -> throwError $ HsenvException $ "Couldn't extract ghc-pkg version number from: " ++ out
    Just versionString -> do
      indentMessages $ trace $ "Found version string: " ++ versionString
      version <- parseVersion versionString
      let ghc_6_12_1_version = Version [6,12,1] []
      if version < ghc_6_12_1_version then do
        indentMessages $ debug "Detected GHC older than 6.12, initializing GHC_PACKAGE_PATH to file with '[]'"
        liftIO $ writeFile (ghcPackagePath dirStructure) "[]"
       else do
        _ <- indentMessages $ insideGhcPkg ["init", ghcPackagePath dirStructure] Nothing
        return ()

-- copy optional packages and don't fail completely if this copying fails
-- some packages mail fail to copy and it's not fatal (e.g. older GHCs don't have haskell2010)
transplantOptionalPackage :: String -> Hsenv ()
transplantOptionalPackage name = transplantPackage (PackageName name) `catchError` handler
  where handler e = do
          warning $ "Failed to copy optional package " ++ name ++ " from system's GHC: "
          indentMessages $ warning $ getExceptionMessage e

-- copy base system
-- base - needed for ghci and everything else
-- Cabal - needed to install non-trivial cabal packages with cabal-install
-- haskell98 - some packages need it but they don't specify it (seems it's an implicit dependancy)
-- haskell2010 - maybe it's similar to haskell98?
-- ghc and ghc-binary - two packages that are provided with GHC and cannot be installed any other way
-- also include dependant packages of all the above
-- when using GHC from tarball, just reuse its package database
-- cannot do the same when using system's GHC, because there might be additional packages installed
-- then it wouldn't be possible to work on them insie virtual environment
copyBaseSystem :: Hsenv ()
copyBaseSystem = do
  info "Copying necessary packages from original GHC package database"
  indentMessages $ do
    ghc <- asks ghcSource
    case ghc of
      System -> do
        transplantPackage $ PackageName "base"
        transplantPackage $ PackageName "Cabal"
        mapM_ transplantOptionalPackage ["haskell98", "haskell2010", "ghc", "ghc-binary"]
      _ -> debug "Using external GHC - nothing to copy, Virtual environment will reuse GHC package database"

installGhc :: Hsenv ()
installGhc = do
  info "Installing GHC"
  ghc <- asks ghcSource
  case ghc of
    System              -> indentMessages $ debug "Using system version of GHC - nothing to install."
    Tarball tarballPath -> indentMessages $ installExternalGhc tarballPath
    Url url             -> indentMessages $ installRemoteGhc url
    Release tag         -> indentMessages $ installReleasedGhc tag

installExternalGhc :: FilePath -> Hsenv ()
installExternalGhc tarballPath = do
  info $ "Installing GHC from " ++ tarballPath
  dirStructure <- hseDirStructure
  runInTmpDir $ do
    debug "Unpacking GHC tarball"
    _ <- indentMessages $ outsideProcess' "tar" [ "xf"
                                               , tarballPath
                                               , "--strip-components"
                                               , "1"
                                               ]
    cwd <- liftIO getCurrentDirectory
    let configureScript = cwd </> "configure"
    debug $ "Configuring GHC with prefix " ++ ghcDir dirStructure
    make <- asks makeCmd
    _ <- indentMessages $ outsideProcess' configureScript ["--prefix=" ++ ghcDir dirStructure]
    debug $ "Installing GHC with " ++ make ++ " install"
    _ <- indentMessages $ outsideProcess' make ["install"]
    return ()

-- Download a file over HTTP using streams, so it
-- has constant memory allocation.
downloadFile :: URL -> FilePath -> Hsenv ()
downloadFile url name = do
  m_ex <- liftIO $ get url $ \response inStream ->
    case getStatusCode response of
      200 -> S.withFileAsOutput name (S.connect inStream) >> return Nothing
      code -> return $ Just $ HsenvException $
        "Failed to download "
          ++ name
          ++ ": http response returned "
          ++ show code
  maybe (return ()) throwError m_ex

installRemoteGhc :: String -> Hsenv ()
installRemoteGhc url = runInTmpDir $ do
    cwd <- liftIO getCurrentDirectory
    let tarball = cwd </> "tarball"
    debug $ "Downloading GHC from " ++ url
    downloadFile (C8.pack url) tarball
    installExternalGhc tarball

installReleasedGhc :: String -> Hsenv ()
installReleasedGhc tag = do
    let url = "http://www.haskell.org/ghc/dist/" ++ tag ++ "/ghc-" ++ tag ++ "-" ++ platform ++ ".tar.bz2"
    installRemoteGhc url

platform :: String
platform = intercalate "-" [arch, if os == "darwin" then "apple" else "unknown", os]

initDotHsenvDir :: Hsenv ()
initDotHsenvDir = do
  dir <- liftIO $ getAppUserDataDirectory "hsenv"
  liftIO $ createDirectoryIfMissing True dir
