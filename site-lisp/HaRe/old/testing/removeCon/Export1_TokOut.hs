module Export1 where

data T a b = C1 a b | C2 b a

f :: T a b -> a
f (C1 x y) = x

g = 54