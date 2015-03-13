module Global1 where

data T = C1 Int Int | C2 Int

f :: T -> Int
f (C1 x y) = x + y
-- f x = 56

g = f (C1 1 2)