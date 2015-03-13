module Show1 (g) where

data T1 = C1 Int Int | C2 Int Int


f :: T1 -> Int
f (C1 x y) = x + y

g = show (f (C1 1 2))



