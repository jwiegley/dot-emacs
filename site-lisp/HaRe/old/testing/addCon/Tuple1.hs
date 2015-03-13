module Tuple1 where


data T a = T1 a | T2 


f :: (Int, T a) -> a -> Int
f (x, T1 o) g = x
f (x, T2) g = x + 1

