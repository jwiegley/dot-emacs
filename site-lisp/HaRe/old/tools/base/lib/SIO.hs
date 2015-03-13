{-+
An IO wrapper monad for redirecting Stdio.
-}
module SIO(SIO,StdIOops(..),runSIO,withStdio,inBase) where
import Prelude hiding (getContents,readFile,writeFile,ioError,catch,putStr)
import AbstractIO as A
import EnvMT as E
import MT(HasBaseMonad(..),HasEnv(..),Z)
import MUtils

newtype SIO a = SIO (WithEnv StdIOops IO a)
              deriving (Functor,Monad,FileIO,SystemIO,DirectoryIO,TimeIO)

data StdIOops = StdIO {put,eput::String->IO (){-, get::IO String-}}

runSIO (SIO m) = withEnv stdIOops m
  where stdIOops = StdIO { put=putStr,eput=ePutStr{-,get=getContents-}}

withStdio ops = E.inEnv (ops::StdIOops)

instance HasEnv SIO Z StdIOops where
  getEnv ix = SIO E.getEnv 
  inEnv _ e (SIO m) = SIO (E.inEnv e m)

--instance HasBaseMonad IO IO where inBase = id

instance HasBaseMonad SIO IO where
  inBase io = SIO $ lift io

stdPut s = do put <- put # E.getEnv
	      inBase (put s)
stdePut s = do put <- eput # E.getEnv
	       inBase (put s)
{-
stdGet = do get <- get # E.getEnv
	    inBase get
-}

instance StdIO SIO where
  putStr = stdPut
  ePutStr = stdePut
  getContents = inBase getContents

instance CatchIO IOError SIO where
  SIO m1 `catch` em2 = 
     SIO $
     m1 `catch` \ e ->
     let SIO m2 = em2 e
     in m2
  ioError = SIO . ioError

instance CatchIO err m => CatchIO err (WithEnv e m) where
  m `catch` f = do e <- E.getEnv
                   lift (withEnv e m `catch` (withEnv e . f))
  ioError = lift . ioError
