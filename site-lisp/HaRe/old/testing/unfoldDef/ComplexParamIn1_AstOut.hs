module ComplexParamIn1 where
sumSquares x y
    =   (case (x, y) of
	     (m, n) -> m ^ n)
 
sq (m, n) = m ^ n
 