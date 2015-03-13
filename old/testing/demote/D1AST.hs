module D1 where
sumSquares ((x : xs)) = sq + (sumSquares xs)
sumSquares [] = 0
 
sq x = x ^ pow
 
pow = 2
 
main = sumSquares [1 .. 4]
 