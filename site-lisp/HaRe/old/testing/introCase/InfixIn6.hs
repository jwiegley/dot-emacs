module InfixIn6 where


data Inf = Nil | Int :* [Int]


f :: (Inf, Either Int Int) -> Int
f (a,b) = hd a 

hd :: Inf -> Int
hd Nil = 0
hd (x :* xs) = x
