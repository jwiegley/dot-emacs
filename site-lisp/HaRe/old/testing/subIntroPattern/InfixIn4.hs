module InfixIn4 where


data Inf a b = Nil | a :* b


f :: Inf [Int] (Either Int Int) -> [Int]
f Nil = []
f (a :* b) = a
