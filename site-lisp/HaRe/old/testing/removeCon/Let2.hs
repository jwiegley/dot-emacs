
module Let2 where

data T1 a b = C1 a b | C2 b a

res2 =  [ f (C1 1 2) | let f (C1 x y) = 1 + 2]

