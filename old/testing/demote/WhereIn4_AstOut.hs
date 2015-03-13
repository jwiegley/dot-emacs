module WhereIn4 where
sumSquares x y
    = (sq x) + (sq y)
  where
      p = 2
      sq z = z ^ p
 
anotherFun 0 y = sq y where sq x = x ^ 2
 