module LetIn1 where
sumSquares x y
    = let in (sq x) + (sq y)
  where
      pow = 2
      sq 0 = 0
      sq z = z ^ pow
 
anotherFun 0 y = sq y where sq x = x ^ 2
 