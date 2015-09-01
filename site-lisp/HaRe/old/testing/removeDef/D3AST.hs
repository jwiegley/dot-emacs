module D3 where
sumSquares ((x : xs)) = (x ^ pow) + (sumSquares xs)
sumSquares [] = 0
 
pow = 2
 
main = sumSquares [1 .. 4]
 