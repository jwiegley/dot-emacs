module IxEnvMT (HasEnv(..), MT(..), at, Z, S, Top, Under, WithEnv, withEnv, mapEnv) where

import MT
import Control_Monad_Fix

import Control.Monad(liftM,MonadPlus(..))


newtype WithEnv e m a = E { unE :: e -> m a }


withEnv :: e -> WithEnv e m a -> m a
withEnv e (E f) = f e

mapEnv :: Monad m => (e2 -> e1) -> WithEnv e1 m a -> WithEnv e2 m a
mapEnv f (E m) = E (\e -> m (f e))


--------------------------------------------------------------------------------
instance Monad m => Functor (WithEnv e m) where
    fmap        = liftM

instance Monad m => Monad (WithEnv e m) where
    return      = lift . return
    E m >>= f   = E (\e -> do x <- m e; unE (f x) e)
    E m >> n    = E (\e -> m e >> withEnv e n)
    fail        = lift . fail

instance MT (WithEnv e) where
    lift        = E . const

instance MonadPlus m => MonadPlus (WithEnv e m) where
    mzero           = lift mzero
    E a `mplus` E b = E (\e -> a e `mplus` b e)
--------------------------------------------------------------------------------


-- Features --------------------------------------------------------------------
instance Monad m => HasEnv (WithEnv e m) Z e where
    getEnv _    = E return
    inModEnv _  = mapEnv

instance HasEnv m ix e => HasEnv (WithEnv e' m) (S ix) e where
    getEnv (Next ix)        = lift (getEnv ix)
    inModEnv (Next ix) f m  = E (\e -> inModEnv ix f (withEnv e m))

instance HasState m ix s => HasState (WithEnv e m) ix s where
    updSt ix  = lift . updSt ix

instance HasOutput m ix o => HasOutput (WithEnv e m) ix o where
    outputTree ix = lift . outputTree ix

instance HasExcept m x => HasExcept (WithEnv e m) x where
    raise           = lift . raise
    handle h (E m)  = E (\e -> handle (withEnv e . h) (m e))

instance HasCont m => HasCont (WithEnv e m) where
    callcc f    = E (\e -> callcc (\k -> withEnv e $ f (lift . k)))

instance MonadFix m => MonadFix (WithEnv e m) where
    mfix f      = E (\e -> mfix (withEnv e . f))

instance HasBaseMonad m n => HasBaseMonad (WithEnv e m) n where
    inBase      = lift . inBase

instance HasRefs m r => HasRefs (WithEnv e m) r where
    newRef   = lift . newRef
    readRef  = lift . readRef
    writeRef r = lift . writeRef r
