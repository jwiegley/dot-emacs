module InfixIn3 where
data Inf a b = Nil | a :* b
 
data Try = C1 Try2
 
data Try2 = C2 [Int]
 
data T = MkT [a]
 
f :: (Inf [Int] (Either Int Int)) -> [Int]
 
f Nil = []
f ((a :* b@(Left b_1))) = a
f ((a :* b@(Right b_1))) = a
f ((a :* b)) = a
 
h :: (Inf [Int] (Either Int Int)) -> [Int]
 
h Nil = []
h ((a@[] :* b)) = a
h ((a@((x : xs)) :* b)) = a
 
j :: Int -> Try -> [Int]
 
j v x@(C1 b_1@(C2 b_2)) = []
j v x@(C1 b_1) = []
j v x = []
 
p :: [a] -> a
 
p ((x : xs)) = x
 