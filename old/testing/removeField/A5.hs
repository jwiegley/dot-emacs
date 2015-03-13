module A5 where

data Data1 a = C1 a Int Char |
              C2 Int        |
	      C3 Float

f :: Data1 a -> Int
f (C1 a b c) = b -- errorData "b" "Data.C1" "f"
f (C2 a) = a
f (C3 a) = 42

g (C1 (C1 x y z) b c) = y
