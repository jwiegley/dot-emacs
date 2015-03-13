{-# LANGUAGE GeneralizedNewtypeDeriving, ScopedTypeVariables #-}
module HsenvMonad ( Hsenv
                  , runHsenv
                  , indentMessages
                  , debug
                  , info
                  , trace
                  , warning
                  , finally
                  , throwError
                  , catchError
                  , ask
                  , asks
                  , gets
                  , tell
                  , modify
                  , liftIO
                  , action
                  ) where

import Types

import Control.Exception as Exception (IOException, catch)
import Control.Monad.Trans (MonadIO, liftIO)
import Control.Monad.Reader (ReaderT, MonadReader, runReaderT, asks, ask)
import Control.Monad.Writer (WriterT, MonadWriter, runWriterT, tell)
import Control.Monad.State (StateT, MonadState, evalStateT, modify, gets)
import Control.Monad.Error (ErrorT, MonadError, runErrorT, throwError, catchError)
import Control.Monad (when)
import System.IO (stderr, hPutStrLn)

import Prelude hiding (log)

newtype Hsenv a = Hsenv (StateT HsenvState (ReaderT Options (ErrorT HsenvException (WriterT [String] IO))) a)
    deriving (Functor, Monad, MonadReader Options, MonadState HsenvState, MonadError HsenvException, MonadWriter [String])

instance MonadIO Hsenv where
    liftIO m = Hsenv $ do
                 x <- liftIO $ (Right `fmap` m) `Exception.catch` \(e :: IOException) -> return $ Left e
                 case x of
                   Left e  -> throwError $ HsenvException $ "IO error: " ++ show e
                   Right y -> return y

runHsenv :: Hsenv a -> Options -> IO (Either HsenvException a, [String])
runHsenv (Hsenv m) = runWriterT . runErrorT . runReaderT (evalStateT m (HsenvState 0))

finally :: Hsenv a -> Hsenv b -> Hsenv a
finally m sequel = do
  result <- (Right `fmap` m) `catchError` (return . Left)
  _ <- sequel
  case result of
    Left e  -> throwError e
    Right x -> return x

indentMessages :: Hsenv a -> Hsenv a
indentMessages m = do
  modify (\s -> s{logDepth = logDepth s + 2})
  result <- m
  modify (\s -> s{logDepth = logDepth s - 2})
  return result

-- add message to private log and return adjusted message (with log depth)
-- that can be printed somewhere else
privateLog :: String -> Hsenv String
privateLog str = do
  depth <- gets logDepth
  let text = replicate (fromInteger depth) ' ' ++ str
  tell [text]
  return text

log :: Verbosity -> String -> Hsenv ()
log minLevel str = do
  text <- privateLog str
  flag <- asks verbosity
  when (flag >= minLevel) $
    liftIO $ putStrLn text

debug :: String -> Hsenv ()
debug = log Verbose

info :: String -> Hsenv ()
info = log Quiet

trace :: String -> Hsenv ()
trace = log VeryVerbose

warning :: String -> Hsenv ()
warning str = do
  text <- privateLog str
  liftIO $ hPutStrLn stderr text

action :: String -> Hsenv a -> Hsenv a
action descr m = info descr >> indentMessages m
