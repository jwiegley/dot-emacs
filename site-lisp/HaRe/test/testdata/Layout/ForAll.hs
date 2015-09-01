{-# LANGUAGE RankNTypes #-}
module Layout.ForAll where

import Data.Data

foo ::  (forall a. Data a => a -> a) -> forall a. Data a => a -> a
foo a = a
