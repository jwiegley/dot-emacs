module Type3 where

data Data a = C1 a Int Char |
              C2 Int       |
	      C3 Float

f :: Data a -> a
f (C1 a b c) = a
f (C2 a)     = a
f (C3 a)     = 42

(C1 (C1 x y z) b c) = 89
