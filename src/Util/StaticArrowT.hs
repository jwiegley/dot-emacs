module Util.StaticArrowT ( StaticArrowT(..)
                         , addStatic
                         , getStatic
                         ) where

import Data.Monoid (Monoid(..))
import Control.Arrow (Arrow(..), ArrowChoice(..))
import qualified Control.Category as C

-- arrow transformer, that adds static information
-- to underlying computation
data StaticArrowT m arr a b = StaticArrowT m (arr a b)

instance (C.Category arr, Monoid m) => C.Category (StaticArrowT m arr) where
  id = StaticArrowT mempty C.id
  StaticArrowT m2 arr2 . StaticArrowT m1 arr1 =
      StaticArrowT (m2 `mappend` m1) $ arr2 C.. arr1

instance (Arrow arr, Monoid m) => Arrow (StaticArrowT m arr) where
  arr f = StaticArrowT mempty $ arr f
  first (StaticArrowT m arrow) = StaticArrowT m $ first arrow

instance (ArrowChoice arr, Monoid m) => ArrowChoice (StaticArrowT m arr) where
    left (StaticArrowT m arrow) = StaticArrowT m $ left arrow

-- simplest computation with specified static information
addStatic :: (Monoid m, Arrow arr) => m -> StaticArrowT m arr a a
addStatic m = StaticArrowT m C.id

-- returns static information from the whole computation
-- (without running it)
getStatic :: (Monoid m, Arrow arr) => StaticArrowT m arr a b -> m
getStatic (StaticArrowT m _) = m
