module Util.IO ( getEnvVar
               , makeExecutable
               , readProcessWithExitCodeInEnv
               , Environment
               , createTemporaryDirectory
               , which
               ) where

import System.Environment (getEnv)
import System.IO.Error (isDoesNotExistError)
import System.Directory (getPermissions, setPermissions, executable, removeFile, createDirectory, doesFileExist)
import Control.Concurrent (forkIO, putMVar, takeMVar, newEmptyMVar)
import Control.Exception as Exception (catch, evaluate)
import System.Process (runInteractiveProcess, waitForProcess)
import System.IO (hGetContents, hPutStr, hFlush, hClose, openTempFile)
import System.Exit (ExitCode)
import Data.List.Split (splitOn)
import Control.Monad (foldM)
import System.FilePath ((</>))

-- Computation getEnvVar var returns Just the value of the environment variable var,
-- or Nothing if the environment variable does not exist
getEnvVar :: String -> IO (Maybe String)
getEnvVar var = Just `fmap` getEnv var `Exception.catch` noValueHandler
    where noValueHandler e | isDoesNotExistError e = return Nothing
                           | otherwise             = ioError e

makeExecutable :: FilePath -> IO ()
makeExecutable path = do
  perms <- getPermissions path
  setPermissions path perms{executable = True}

type Environment = [(String, String)]

-- like readProcessWithExitCode, but takes additional environment argument
readProcessWithExitCodeInEnv :: Environment -> FilePath -> [String] -> Maybe String -> IO (ExitCode, String, String)
readProcessWithExitCodeInEnv env progName args input = do
  (inh, outh, errh, pid) <- runInteractiveProcess progName args Nothing (Just env)
  out <- hGetContents outh
  outMVar <- newEmptyMVar
  _ <- forkIO $ evaluate (length out) >> putMVar outMVar ()
  err <- hGetContents errh
  errMVar <- newEmptyMVar
  _ <- forkIO $ evaluate (length err) >> putMVar errMVar ()
  case input of
    Just inp | not (null inp) -> hPutStr inh inp >> hFlush inh
    _ -> return ()
  hClose inh
  takeMVar outMVar
  hClose outh
  takeMVar errMVar
  hClose errh
  ex <- waitForProcess pid
  return (ex, out, err)

-- similar to openTempFile, but creates a temporary directory
-- and returns its path
createTemporaryDirectory :: FilePath -> String -> IO FilePath
createTemporaryDirectory parentDir templateName = do
  (path, handle) <- openTempFile parentDir templateName
  hClose handle
  removeFile path
  createDirectory path
  return path

which :: Maybe String -> String -> IO (Maybe FilePath)
which pathVar name = do
  path <- case pathVar of
           Nothing   -> getEnvVar "PATH"
           Just path -> return $ Just path
  case path of
    Nothing    -> return Nothing
    Just path' -> do
      let pathElems = splitOn ":" path'
          aux x@(Just _) _ = return x
          aux Nothing pathDir = do
            let programPath = pathDir </> name
            flag <- doesFileExist programPath
            if flag then
                return $ Just programPath
             else
                return Nothing
      foldM aux Nothing pathElems
