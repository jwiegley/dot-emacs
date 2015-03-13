module InfixIn4 where
data Inf a b = Nil | a :* b
 
f :: (Inf [Int] (Either Int Int)) -> [Int]
 
f Nil = []
f ((a@[] :* b)) = a
f ((a@(b_1 : b_2) :* b)) = a
f ((a :* b)) = a
 