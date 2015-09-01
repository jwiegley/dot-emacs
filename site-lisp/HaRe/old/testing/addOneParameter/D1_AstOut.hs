module D1 where
sumSquares ((x : xs))
    = ((sq sq_f) x) + (sumSquares xs)
sumSquares [] = 0
 
sq f x = x ^ pow
 
sq_f = undefined
 
pow = 2
 