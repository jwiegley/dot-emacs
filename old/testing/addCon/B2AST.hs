module B2 where
data Data1 a
    = C1 a Int Int | C4 Float | C2 Int | C3 Float
 
addedC4 = error "added C4 Float to Data1"
 
g (C1 x y z) (C1 n m o) = y + m
g (C4 a) b = addedC4
g a (C4 b) = addedC4
g (C2 x) (C2 y) = x - y
g (C3 x) (C3 k) = 42
 