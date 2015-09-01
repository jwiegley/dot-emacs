module D2 where
sumSquares ((x : xs))
    = ((sq pow) x) + (sumSquares xs) where pow = 2
sumSquares [] = 0
 
sq pow x = x ^ pow
 