module Tuple2 where


data T a = T1 a | T2 


f :: (Int, T b) -> a -> Int
f (x, T1 o) g = x
f (x, T2) g = x + 1

