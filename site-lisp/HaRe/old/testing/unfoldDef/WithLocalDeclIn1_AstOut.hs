module WithLocalDeclIn1 where
sumSquares x y
    =   (case x of
	     0 -> 0
	     x -> x ^ pow where pow = 2) +
	    (sq y)
 
sq 0 = 0
sq x = x ^ pow where pow = 2
 