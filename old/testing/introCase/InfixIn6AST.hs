module InfixIn6 where
data Inf = Nil | Int :* [Int]
 
f :: (Inf, Either Int Int) -> Int
 
f (a, b)
    =   case a of
            a@Nil -> hd a
            a@(b_1 :* b_2) -> hd a
f (a, b) = hd a
 
hd :: Inf -> Int
 
hd Nil = 0
hd ((x :* xs)) = x
 