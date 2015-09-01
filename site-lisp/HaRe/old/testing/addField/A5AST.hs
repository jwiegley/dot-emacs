module A5 where
data Data1 b a = C1 a Int Char | C2 Int | C3 b Float
 
f :: (Data1 b a) -> Int
 
f (C1 a b c) = b
f (C2 a) = a
f (C3 a) = 42
 
g (C1 (C1 x y z) b c) = y
 
h :: Data1 b a
 
h = C2 42
 