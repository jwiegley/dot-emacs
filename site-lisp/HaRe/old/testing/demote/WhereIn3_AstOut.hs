module WhereIn3 where
sumSquares x y
    = (sq p x) + (sq p y)
  where
      p = 2
      sq :: Int -> Int -> Int
      sq pow 0 = 0
      sq pow z = z ^ pow
 
anotherFun 0 y = sq y where sq x = x ^ 2
 