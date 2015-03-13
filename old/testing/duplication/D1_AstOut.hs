module D1 (sumSquares) where
sumSquares ((x : xs))
    = (sq x) + (sumSquares xs)
  where
      sq x = x ^ pow
      pow = 2
sumSquares [] = 0
 
anotherFun ((x : xs))
    = (sq x) + (anotherFun xs)
  where
      sq x = x ^ pow
      pow = 2
anotherFun [] = 0
 