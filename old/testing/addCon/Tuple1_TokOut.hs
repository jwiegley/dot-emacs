module Tuple1 where


data T b a = T1 a  | T3 b  | T2 


addedT3 = error "added T3 b to T"
f :: (Int, T b a) -> a -> Int
f (x, (T3 a)) a = addedT3
f (x, T1 o) g = x
f (x, T2) g = x + 1

