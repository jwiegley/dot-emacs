module D1 where
sumSquares ((x : xs))
    = sq + (sumSquares xs) where sq = x ^ pow
sumSquares [] = 0
 
pow = 2
 
main = sumSquares [1 .. 4]
 