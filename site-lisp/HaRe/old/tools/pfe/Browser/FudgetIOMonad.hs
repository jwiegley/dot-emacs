module FudgetIOMonad where
import Prelude hiding (readFile,writeFile,
		       putStr,putStrLn,getLine,readLn,print,
		       catch,ioError)
import AllFudgets
import AbstractIO
import DialogueIO as D
import MUtils
import MT (MT(..))

newtype FIOM f i o a = M {unM::(a->f i o)->(D.IOError->f i o)->f i o}

runFIOM (M m) = m (const end) (error.show)

instance Functor (FIOM f i o) where
  fmap f (M m) = M $ \ c h -> m (c.f) h

instance Monad (FIOM f i o) where
  return x = M $ \ c h -> c x
  M m1>>=xm2 = M $ \ c h -> m1 (\x->unM (xm2 x) c h) h
  fail s = M $ \ c h -> h (OtherError s)
--------------------------------------------------------------------------------

getFM = M $ \ c h -> get c
putFM x = M $ \ c h -> put x (c ())

{- -- This causes weird type checking problems with GHC. Overlapping instances?
class Monad m => SPIO m i o | m -> i o where
  putM :: o -> m ()
  getM :: m i

instance StreamProcIO f => SPIO (FIOM f i o) i o where
  putM = putFM
  getM = getFM

instance (Monad (t m),MT t,SPIO m i o) => SPIO (t m) i o where
  putM = lift . putM
  getM = lift getM
-}
--------------------------------------------------------------------------------

instance FudgetIO f => FileIO (FIOM f i o) where
  readFile = strIO . ReadFile
  writeFile path s = succIO (WriteFile path s)

instance CatchIO D.IOError (FIOM f i o) where
  M m `catch` h = M $ \ c h' -> m c (\e->unM (h e) c h')
  ioError e = M $ \ _ h -> h e

instance FudgetIO f => DirectoryIO (FIOM f i o) where
  createDirectory path = succIO (CreateDirectory path "")
  removeFile = succIO . DeleteFile
  getDirectoryContents = strListIO . ReadDirectory
  doesDirectoryExist path = (((==)"d").take 1) # statusFile path

statusFile = strIO . StatusFile

instance FudgetIO f => SystemIO (FIOM f i o) where
  system cmd = succIO (System cmd) >> return ExitSuccess -- !!


instance IOErr D.IOError where
  isDoesNotExistError (ReadError _) = True
  isDoesNotExistError _ = False

--------------------------------------------------------------------------------

strIO req = ansIO req (\(Str s)->s)
strListIO req =ansIO req (\(StrList s)->s)
succIO req = ansIO req (\Success->())
ansIO req proj = M $ \ c h -> hIOerr req h (c.proj)
