module InfixIn4 where
data Inf a b = Nil | a :* b
 
f :: (Inf [Int] (Either Int Int)) -> [Int]
 
f Nil = []
f ((a :* b))
    =   case a of
            a@[] -> a
            a@(b_1 : b_2) -> a
f ((a :* b)) = a
 