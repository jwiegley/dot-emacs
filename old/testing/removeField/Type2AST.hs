module Type2 where
data Data a = C1 Int Char | C2 Int a | C3 Float
 
f :: Data -> Int
 
f (C1 b c) = b
f (C2 a) = a
f (C3 a) = 42
 
(C1 b c) = 89
 