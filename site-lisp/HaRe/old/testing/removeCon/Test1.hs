module Test1 where

data T = C1 Int

f :: T -> Int
f (C1 x) = x
-- f x = 42

j = f (C1 42) 



