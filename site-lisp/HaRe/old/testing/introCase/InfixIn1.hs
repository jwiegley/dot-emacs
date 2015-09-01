module Infix1 where


data Inf = Nil | Int :* [Int]


f :: Inf -> Int
f Nil = 0
f (x :* xs) = x + head xs