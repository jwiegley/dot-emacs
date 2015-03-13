import Control.Monad (when)
import System.IO (stderr, hPutStrLn)
import System.Exit (exitFailure)
import System.FilePath ((</>))

import Types
import HsenvMonad
import Actions
import SanityCheck (sanityCheck)
import Args (getArgs)
import Paths (dotDirName, constructDotDirName)

main :: IO ()
main = do
  options <- getArgs
  (result, messageLog) <- runHsenv realMain options
  case result of
    Left err -> do
                hPutStrLn stderr $ getExceptionMessage err
                hPutStrLn stderr ""
                hPutStrLn stderr "hsenv.log file contains detailed description of the process."
                let errorLog = unlines $ messageLog ++ ["", getExceptionMessage err]
                writeFile "hsenv.log" errorLog
                exitFailure
    Right ()  -> do
                let dotDir = constructDotDirName options
                writeFile (dotDir </> "hsenv.log") $ unlines messageLog

realMain :: Hsenv ()
realMain = do
  initDotHsenvDir
  skipSanityCheckFlag <- asks skipSanityCheck
  if skipSanityCheckFlag then
      info "WARNING: sanity checks are disabled."
   else
      sanityCheck
  createDirStructure
  installGhc
  initGhcDb
  copyBaseSystem
  installCabalConfig
  installActivateScript
  installCabalWrapper
  installSimpleWrappers
  installProgSymlinks
  symlinkToSkeleton "runghc" "runhaskell"
  bootstrapCabalFlag <- asks cabalBootstrap
  when bootstrapCabalFlag bootstrapCabal
  cabalUpdate
  info ""
  dotDir <- dotDirName
  info $ "To activate the new environment use 'source " ++ dotDir ++ "/bin/activate'"
