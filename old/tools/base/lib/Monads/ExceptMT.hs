{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances, UndecidableInstances, FunctionalDependencies, NoMonomorphismRestriction #-}
module ExceptMT (HasExcept(..), MT(..), WithExcept, removeExcept, mapExcept)
  where

import MT
import Control_Monad_Fix

import Control.Monad(liftM,MonadPlus(..))

newtype WithExcept x m a   = E { removeExcept :: m (Either x a) }
iso f = E . f . removeExcept


mapExcept :: Monad m => (x -> y) -> WithExcept x m a -> WithExcept y m a
mapExcept f = iso (liftM (either (Left . f) Right))


--------------------------------------------------------------------------------
instance Monad m => Functor (WithExcept x m) where
  fmap = liftM

instance Monad m => Monad (WithExcept x m) where
  return    = lift . return
  E m >>= f = E $ do x <- m
                     case x of
                       Left x  -> return (Left x)
                       Right a -> removeExcept (f a)

instance MT (WithExcept x) where
  lift m    = E (m >>= return . Right)

instance MonadPlus m => MonadPlus (WithExcept x m) where
  mzero             = lift mzero
  E m1 `mplus` E m2 = E (m1 `mplus` m2)
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
instance HasEnv m ix e => HasEnv (WithExcept x m) ix e where
  getEnv ix       = lift (getEnv ix)
  inModEnv ix f   = iso (inModEnv ix f)

instance HasState m ix s => HasState (WithExcept x m) ix s where
  updSt ix        = lift . updSt ix

instance HasOutput m ix o => HasOutput (WithExcept x m) ix o where
  outputTree ix   = lift . outputTree ix

instance Monad m => HasExcept (WithExcept x m) x where
  raise           = E . return . Left
  handle h (E m)  = E (m >>= either (removeExcept . h) (return . Right))

instance HasCont m => HasCont (WithExcept x m) where
  callcc f        = E $ callcc $ \k -> removeExcept $ f $ E . k . Right


instance HasBaseMonad m n => HasBaseMonad (WithExcept e m) n where
  inBase          = lift . inBase

instance HasRefs m r => HasRefs (WithExcept x m) r where
  newRef          = lift . newRef
  readRef         = lift . readRef
  writeRef r      = lift . writeRef r


instance MonadFix m => MonadFix (WithExcept x m) where
  mfix f          = E $ mfix (removeExcept . f . either undefined id)


