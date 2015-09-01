{-# OPTIONS_GHC -cpp #-}
{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances, UndecidableInstances, FunctionalDependencies, NoMonomorphismRestriction #-}
module ExceptM (module ExceptM, HasExcept(..)) where

import MT
import Control_Monad_Fix

import Control.Monad (liftM)

{- use newtype to avoid conflicts with class instances! -}
newtype ExceptM l r      = ExceptM {removeExcept :: Either l r}

{- not used
removeExcept          :: ExceptM x a -> Either x a
removeExcept          = id

mapEither f g         = either (Left . f) (Right . g)
seqEither x           = either (fmap Left) (fmap Right) x

fromEither f (Right x)= x
fromEither f (Left x) = f x

unLeft (Left x)       = x
unLeft _              = error "unLeft"
-}

unRight (ExceptM (Right x)) = x
unRight _                   = error "unRight"

instance Functor (ExceptM x) where
  fmap                = liftM

instance Monad (ExceptM x) where
  return                  = ExceptM . Right
  ExceptM (Right x) >>= f = f x
  ExceptM (Left x) >>= f  = ExceptM (Left x)

  ExceptM (Right _) >> m  = m
  ExceptM (Left x) >> m   = ExceptM (Left x)
    

instance HasExcept (ExceptM x) x where
  raise               = ExceptM . Left
  handle h (ExceptM (Left x))   = h x
  handle h (ExceptM (Right x))  = ExceptM (Right x)
  

instance MonadFix (ExceptM x) where
  mfix f              = let a = f (unRight a) in a

instance HasBaseMonad (ExceptM x) (ExceptM x) where
  inBase              = id    


