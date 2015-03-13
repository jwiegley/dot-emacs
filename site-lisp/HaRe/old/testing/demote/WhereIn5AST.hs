module WhereIn5 where
sumSquares x y
    = (sq x) + (sq y)
  where
      sq 0 = 0
      sq z = z ^ pow
      pow = 2
 
pow = 2
 
anotherFun 0 y = sq y where sq x = x ^ 2
 