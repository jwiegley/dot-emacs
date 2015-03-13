{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
module IxOutputM 
  (HasOutput(..), OutputM, foldOutput, listOutput, mapOutput) where

import MT
import Control_Monad_Fix

import Tree

data OutputM o a = O a (Tree o)


foldOutput :: b -> (o -> b) -> (b -> b -> b) -> OutputM o a -> (a,b)
foldOutput e s j (O x tree)  = (x, Tree.fold e s j tree)

listOutput :: OutputM o a -> (a,[o])
listOutput (O x o)          = (x, Tree.toList o)

mapOutput :: (o -> p) -> OutputM o a -> OutputM p a
mapOutput f (O x tree)      = O x (fmap f tree)


instance Functor (OutputM o) where
    fmap f (O x o)          = O (f x) o

instance Monad (OutputM o) where
    return x                = O x Tree.Empty
    O x o >>= f             = let O y p = f x in O y (o `Tree.merge` p)
    O x o >> O y p          = O y (o `Tree.merge` p)

instance HasOutput (OutputM o) Z o where
    outputTree _ t          = O () t

instance MonadFix (OutputM o) where
    mfix f = let it@(O a _) = f a in it

instance HasBaseMonad (OutputM o) (OutputM o) where
  inBase = id
