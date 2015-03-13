module LetIn2 where
sumSquares x y
    = let pow = 2 in ((sq pow) x) + ((sq pow) y)
  where
      sq pow 0 = 0
      sq pow z = z ^ pow
 
anotherFun 0 y = sq y where sq x = x ^ 2
 