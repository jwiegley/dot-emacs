module A1 where

data Data a = C1 a Int Char |
              C2 a Int        |
	      C3 Float

f :: Data a -> Int
f (C1 a b c) = b
f (C2 c2_1 a)     = a
f (C3 a)     = 42

(C1 (C1 x y z) b c) = 89
