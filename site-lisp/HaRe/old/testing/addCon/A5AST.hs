module A5 where
data T a = T1 a | T2 Int
 
data S = C1 | C2 | C3
 
addedT2 = error "added T2 Int to T"
 
over :: S -> (T Int) -> Int
 
over a (T2 b) = addedT2
over C1 x = 42
over C2 x = 43
over C3 x = 43
 