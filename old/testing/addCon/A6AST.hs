module A6 where
data T a = T1 a | T3 a | T2 a
 
data S = C1 | C2 | C3
 
addedT3 = error "added T3 a to T"
 
over :: S -> (T Int) -> Int
 
over a (T3 b) = addedT3
over x (T1 y) = 42
over x (T2 y) = 42
 