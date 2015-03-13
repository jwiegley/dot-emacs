module B1 where
data Data1 a
    = C1 a Int Int | C4 Float | C2 Int | C3 Float
 
addedC4 = error "added C4 Float to Data1"
 
g (C1 x y z) = y
g (C4 a) = addedC4
g (C2 x) = x
g (C3 x) = 42
 