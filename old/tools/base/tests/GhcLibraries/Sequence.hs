-- Dummy Sequence module
module Sequence where

import Monad

class (Functor s, MonadPlus s) => Sequence s where
  empty     :: s a

instance Sequence [] where
  empty = []
