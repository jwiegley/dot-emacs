module FudgetIOMonad1 where
import Prelude hiding (readFile,writeFile,
		       putStr,putStrLn,getLine,readLn,print,
		       catch,ioError)
import AllFudgets as F
import AbstractIO as A
import DialogueIO as D
import MUtils
--import MT

import PfePlumbing


{-+
To avoid a problem with overlapping instances in the MT class,
the types of the streams are hardwired...
-}
type PfeF = F In (Either String Out)

newtype FIOM a = M {unM::(a->PfeF)->(D.IOError->PfeF)->PfeF}

runFIOM (M m) = m (const end) (error.show)

instance Functor FIOM where
  fmap f (M m) = M $ \ c h -> m (c.f) h

instance Monad FIOM where
  return x = M $ \ c h -> c x
  M m1>>=xm2 = M $ \ c h -> m1 (\x->unM (xm2 x) c h) h
  fail s = M $ \ c h -> h (OtherError s)
--------------------------------------------------------------------------------

getFM = M $ \ c h -> get c
putFM x = M $ \ c h -> put x (c ())

quitFM = succIO (Exit 0)

{-
class Monad m => SPIO m where
  putM :: Out -> m ()
  getM :: m In

instance SPIO FIOM where
  putM = putFM
  getM = getFM

instance (Monad (t m),MT t,SPIO m) => SPIO (t m) where
  putM = lift . putM
  getM = lift getM
-}
--------------------------------------------------------------------------------

instance FileIO FIOM where
  readFile = strIO . ReadFile
  writeFile path s = succIO (WriteFile path s)

instance StdIO FIOM where
  putStr s = succIO (AppendChan "stdout" s)
  ePutStr s = succIO (AppendChan "stderr" s)

instance CatchIO D.IOError FIOM where
  M m `catch` h = M $ \ c h' -> m c (\e->unM (h e) c h')
  ioError e = M $ \ _ h -> h e

instance DirectoryIO FIOM where
  createDirectory path = succIO (CreateDirectory path "")
  removeFile = succIO . DeleteFile
  getDirectoryContents = strListIO . ReadDirectory
  doesDirectoryExist path = catchFalse $ (((==)"d").take 1) # statusFile path
  doesFileExist path = catchFalse $ (((==)"f").take 1) # statusFile path
  getModificationTime path = M $ flip (F.getModificationTime path)

statusFile = strIO . StatusFile
catchFalse io = io `catch` const (return False)

instance SystemIO FIOM where
  --system cmd = succIO (System cmd) >> return ExitSuccess -- !!
  system cmd = M $ \ c h -> hIOerr (System cmd) (c.exitcode)
					        (c.const ExitSuccess)
    where exitcode (OtherError s) = ExitFailure . read . last .  words $ s
          exitcode _ = ExitFailure 99 -- hmm
  getEnv = strIO . GetEnv
  getProgName = return progName
  getArgs = return args -- Does not include options!

instance TimeIO FIOM where
  getClockTime = xrequestFIOM getTime

instance IOErr D.IOError where
  isDoesNotExistError (ReadError _) = True
  isDoesNotExistError _ = False
  ioeGetErrorString err =
    case err of
      OtherError s -> s
      _ -> show err -- hmm!
  userError = OtherError -- hmm!
  isUserError _ = False

--------------------------------------------------------------------------------

strIO req = ansIO req (\(Str s)->s)
strListIO req =ansIO req (\(StrList s)->s)
succIO req = ansIO req (\Success->())
ansIO req proj = M $ \ c h -> hIOerr req h (c.proj)
xrequestFIOM req = M $ \ c h -> req c
