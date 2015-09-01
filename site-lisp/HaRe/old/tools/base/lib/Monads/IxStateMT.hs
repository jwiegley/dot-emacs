{-# OPTIONS_GHC -cpp  #-}
{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances, UndecidableInstances, FunctionalDependencies, NoMonomorphismRestriction #-}
module IxStateMT (HasState(..), MT, at, Z, S, Top, Under,
                  WithState, withSt, withStS, mapState) where

import MT
import Control_Monad_Fix

import Control.Monad(liftM,MonadPlus(..))


newtype WithState s m a = S { ($$) :: s -> m (a,s) }

withSt :: Monad m => s -> WithState s m a -> m a
withSt s = liftM fst . withStS s

withStS :: s -> WithState s m a -> m (a,s)
withStS s (S f) = f s

mapState :: Monad m =>
            (t -> s) -> (s -> t) -> WithState s m a -> WithState t m a
mapState inF outF (S m) = S (liftM outF' . m . inF)
  where outF' (a,s) = (a, outF s)



--------------------------------------------------------------------------------
instance Monad m => Functor (WithState s m) where
  fmap        = liftM

instance Monad m => Monad (WithState s m) where
  return x    = S (\s -> return (x,s))
  S m >>= f   = S (\s -> m s >>= \(a,s') -> f a $$ s')
  fail msg    = S (\s -> fail msg)

instance MT (WithState s) where
  lift m      = S (\s -> do a <- m; return (a,s))

instance MonadPlus m => MonadPlus (WithState s m) where
  mzero             = lift mzero
  S m1 `mplus` S m2 = S (\s -> m1 s `mplus` m2 s)
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
instance HasEnv m ix e => HasEnv (WithState s m) ix e where
  getEnv ix           = lift (getEnv ix)
  inModEnv ix f (S m) = S (inModEnv ix f . m)

instance Monad m => HasState (WithState s m) Z s where
  updSt _ f       = S (\s -> return (s, f s))

instance HasState m ix s => HasState (WithState s' m) (S ix) s where
  updSt (Next ix) = lift . updSt ix

instance HasOutput m ix o => HasOutput (WithState s m) ix o where
  outputTree ix   = lift . outputTree ix

instance HasExcept m x => HasExcept (WithState s m) x where
  raise           = lift . raise
  handle f (S m)  = S (\s -> handle (withStS s . f) (m s))

-- jumping undoes effects
instance HasCont m => HasCont (WithState s m) where
   callcc f       = S $ \s -> callcc $ \break -> withStS s $ f $ \a -> lift $ break (a,s)
--   callcc f       = S $ \s -> callcc $ \break -> withStS s $ f $ \a -> S $ \s' -> break (a,s')
-- jumping preserves effects



instance HasBaseMonad m n => HasBaseMonad (WithState s m) n where
    inBase      = lift . inBase

instance HasRefs m r => HasRefs (WithState o m) r where
    newRef      = lift . newRef
    readRef     = lift . readRef
    writeRef r  = lift . writeRef r


instance MonadFix m => MonadFix (WithState s m) where
  mfix f = S (\s -> mfix $ \ ~(a,_) -> withStS s (f a))



