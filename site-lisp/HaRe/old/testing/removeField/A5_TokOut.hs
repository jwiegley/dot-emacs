module A5 where

data Data1 a = C1 a Char |
              C2 Int        |
	      C3 Float

errorData field dat function
    =   errorData1
            ("the binding for " ++ field ++ " in a pattern binding involving " ++ dat ++ " has been removed in function " ++ function)

f :: Data1 a -> Int
f (C1 a  c) = errorData1 "b" "C1" "f" -- errorData "b" "Data.C1" "f"
f (C2 a) = a
f (C3 a) = 42

g (C1 (C1 x  z)  c) = errorData1 "y" "C1" "g"
