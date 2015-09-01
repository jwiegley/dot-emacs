module Infix1 where


data Inf = Nil | Int :* [Int]


f :: Inf -> Int
f Nil = 0
f ((x :* xs@[])) = x + (head xs)
f ((x :* xs@(b_1 : b_2))) = x + (head xs)
f ((x :* xs)) = x + (head xs)