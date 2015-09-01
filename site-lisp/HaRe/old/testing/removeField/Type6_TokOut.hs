module Type6 where

data Data b = C1 Int Char | C2 Int b | C3 Float

errorData field dat function
    =   errorData
            ("the binding for " ++ field ++ " in a pattern binding involving " ++ dat ++ " has been removed in function " ++ function)

f :: (Data b) -> (Data b) -> a
f (C1  b c) (C1  b1 b2) = errorData "a1" "C1" "f"
f (C2 a)     = a
f (C3 a)     = 42

(C1  b c) = 89

g :: (Data b) -> Int
g (C3 a) = 42 
