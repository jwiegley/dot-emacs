module A3 where

data T a = C1 a 


over :: (T b) -> b
over (C1 x) = x

