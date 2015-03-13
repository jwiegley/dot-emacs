module A2 where
data Data a = C1 a Int | C2 Int | C3 Float
 
f :: (Data a) -> Int
 
f (C1 a b) = 99
f (C2 a) = a
f (C3 a) = 42
 
(C1 (C1 x y) b) = 89
 