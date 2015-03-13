module A4 where

data Data a = C1 a Int Char |
              C2 Int        |
	      C3 Float

f :: Data a -> Int
f (C1 a b c) = 99
f (C2 a) = a
f (C3 a) = 42

g (C1 (C1 x y z) b c) = 89
