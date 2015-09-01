module WhereIn6 where
sumSquares x y
    = (sq x) + (sq y)
  where
      sq :: Int -> Int
      sq 0 = 0
      sq z = z ^ pow
      pow = 2
 
anotherFun 0 y = sq y where sq x = x ^ 2
 