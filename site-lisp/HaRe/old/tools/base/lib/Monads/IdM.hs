{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances, UndecidableInstances, FunctionalDependencies, NoMonomorphismRestriction #-}
module IdM where

import MT
import Control_Monad_Fix


newtype IdM a   = I { removeId :: a }

instance Monad IdM where
  return        = I
  I x >>= f     = f x

instance Functor IdM where
  fmap f (I x)  = I (f x)

instance HasBaseMonad IdM IdM where
  inBase        = id

instance MonadFix IdM where
  mfix f        = let r@(I x) = f x in r

