module D2 (sumSquares) where
import C2
sumSquares ((x : xs)) = (sq x) + (sumSquares xs)
sumSquares [] = 0
 
sq x = x ^ pow
 
pow = 2
 