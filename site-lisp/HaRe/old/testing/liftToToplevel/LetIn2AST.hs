module LetIn2 where
sumSquares x y
    = let pow = 2 in ((sq pow) x) + ((sq pow) y)
 
sq 0 = 0
sq z = z ^ pow
 
anotherFun 0 y = sq y where sq x = x ^ 2
 