module A2 where
data T a = C1 a | C2 Int
 
addedC2 = error "added C2 Int to T"
 
over :: (T b) -> b
 
over (C1 x) = x
over (C2 a) = addedC2
 