module A5 where

data Data1 a = a `C1` Int |
              C2 Int        |
	      C3 Float

f :: Data1 a -> Int
f (a `C1` b) = b -- errorData "b" "Data.C1" "f"
f (C2 a) = a
f (C3 a) = 42

g (x `C1` y)  = y
