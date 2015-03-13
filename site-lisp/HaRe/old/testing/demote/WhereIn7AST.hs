module WhereIn7 where
sumSquares x y
    = (sq x) + (sq y)
  where
      sq :: Int -> Int
      sq 0 = 0
      sq z = z ^ pow where pow = 2
 
sq,anotherFun :: Int -> Int
 
sq 0 = 0
sq z = z ^ pow where pow = 2
 
anotherFun x = x ^ 2
 