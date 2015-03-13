module IdMT where

import MT
import Control_Monad_Fix
import Control.Monad(liftM)


newtype With_ m a    = I { removeId :: m a }


instance MT With_ where
  lift              = I

instance Monad m => Monad (With_ m) where
  return            = lift . return
  I m >>= f         = I (m >>= removeId . f)

instance Monad m => Functor (With_ m) where
  fmap              = liftM

instance HasBaseMonad m n => HasBaseMonad (With_ m) n where
  inBase            = I . inBase

instance HasEnv m ix e => HasEnv (With_ m) ix e where
  getEnv            = I . getEnv

instance HasState m ix e => HasState (With_ m) ix e where
  updSt ix          = I . updSt ix

instance HasOutput m ix o => HasOutput (With_ m) ix o where
  outputTree ix     = I . outputTree ix

instance HasExcept m x => HasExcept (With_ m) x where
  raise             = I . raise
  handle h          = I . handle (removeId . h) . removeId

instance HasCont m => HasCont (With_ m) where
  callcc f          = I (callcc f')
    where f' k      = removeId (f (I . k))

instance HasRefs m r => HasRefs (With_ m) r where
  newRef            = I . newRef
  readRef           = I . readRef
  writeRef r        = I . writeRef r

instance MonadFix m => MonadFix (With_ m) where
  mfix f            = I (mfix (removeId . f))


