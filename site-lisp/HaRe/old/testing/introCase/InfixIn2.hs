module InfixIn2 where


data Inf a b = Nil | a :* b


f :: Inf [Int] [Float] -> [Int]
f Nil = []
f (a :* b) = a
