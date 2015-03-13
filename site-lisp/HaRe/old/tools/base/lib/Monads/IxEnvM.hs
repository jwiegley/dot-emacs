{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances, UndecidableInstances, FunctionalDependencies, NoMonomorphismRestriction,TypeSynonymInstances, FlexibleInstances #-}
module IxEnvM (HasEnv(..), EnvM, withEnv) where

import MT
import Control_Monad_Fix


newtype EnvM e a  = E { ($$) :: e -> a }

withEnv :: e -> EnvM e a -> a
withEnv e f       = f $$ e 

mapEnv :: (e2 -> e1) -> EnvM e1 a -> EnvM e2 a
mapEnv f (E g)    = E (g . f)

instance Functor (EnvM e) where
  fmap f (E g)    = E (f . g)

instance Monad (EnvM e) where
  return x        = E (\e -> x)
  f >>= g         = E (\e -> g (f $$ e) $$ e)
  f >> g          = g

instance HasEnv (EnvM e) Top e where
  getEnv _        = E (\e -> e)
  inModEnv _      = mapEnv 
  inEnv _ e f     = return (f $$ e) 

instance MonadFix (EnvM e) where
  mfix f          = E (\e -> let a = f a $$ e in a)

instance HasBaseMonad (EnvM e) (EnvM e) where
  inBase          = id

