module A4 where

data T a = C1 a 


over :: (T b) -> b
over (C1 x) = x

under :: (T a) -> a
under (C1 x) = x
