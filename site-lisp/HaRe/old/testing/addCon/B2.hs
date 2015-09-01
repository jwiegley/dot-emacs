module B2 where

data Data1 a = C1 a Int Int | C2 Int | C3 Float


g (C1 x y z) (C1 n m o) = y + m
g (C2 x)  (C2 y)  = x - y
g (C3 x)  (C3 k)   = 42


