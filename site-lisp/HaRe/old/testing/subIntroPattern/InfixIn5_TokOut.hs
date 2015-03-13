module InfixIn5 where


data Inf = Nil | Int :* [Int]


f :: (Inf, Either Int Int) -> Int
f (a, b@(Left b_1)) = hd a
f (a, b@(Right b_1)) = hd a
f (a, b) = hd a

hd :: Inf -> Int
hd Nil = 0
hd (x :* xs) = x 
