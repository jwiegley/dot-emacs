module D1 where
sumSquares ((x : xs))
    = ((sq pow) x) + (sumSquares xs) where pow = 2
sumSquares [] = 0
 
sq x = x ^ pow
 
main = sumSquares [1 .. 4]
 