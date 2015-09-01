module Infix1 where

data T1 = C1 Int Int | C2 Int Int

g = f (C1 1 2) + f (C1 2 3)
     where
       f (C1 x y) = x + y