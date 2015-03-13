module MultiMatchesIn2 where
sumSquares x y
    =   (case x of
	     0 -> 0
	     x -> x ^ pow) +
	    (sq y)
  where
      sq 0 = 0
      sq x = x ^ pow
 
pow = 2
 