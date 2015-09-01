module Type3 where

data Data = C1 Int Char | C2 Int | C3 Float

errorData field dat function
    =   errorData
            ("the binding for " ++ field ++ " in a pattern binding involving " ++ dat ++ " has been removed in function " ++ function)
f :: Data -> a
f (C1  b c) = errorData "a" "C1" "f"

f (C2 a)     = a
f (C3 a)     = 42

(C1  b c) = 89

