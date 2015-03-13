module B1 where

data Data1 a = C1 a Int Int | C2 Int | C3 Float


g (C1 x y z) = y
g (C2 x)     = x
g (C3 x)     = 42


