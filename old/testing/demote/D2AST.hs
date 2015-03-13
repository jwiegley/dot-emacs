module D2 where
sq x = x ^ pow
 
pow = 2
 
main
    = sumSquares [1 .. 4]
  where
      sumSquares ((x : xs)) = (sq x) + (sumSquares xs)
      sumSquares [] = 0
 