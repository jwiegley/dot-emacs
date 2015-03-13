module B2 where
data Data1 a = C1 a Int | C2 Int | C3 Float
 
errorData field dat function
    =   errorData1
            ("the binding for " ++ field ++ " in a pattern binding involving " ++ dat ++ " has been removed in function " ++ function)
 
g = (C1 1 3)
 
f   =   do (C1 x z) <- return (C1 1 3)
           let bob = (errorData1 "y" "C1" "f") + 42
           return bob
 