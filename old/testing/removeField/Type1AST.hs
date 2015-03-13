module Type1 where
data Data = C1 Int Char | C2 Int | C3 Float
 
f :: Data -> Int
 
f (C1 b c) = b
f (C2 a) = a
f (C3 a) = 42
 
(C1 b c) = 89
 