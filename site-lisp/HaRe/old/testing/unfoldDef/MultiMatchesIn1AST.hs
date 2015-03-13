module MultiMatchesIn1 where
sumSquares x y
    =   (case x of
             0 -> 0
             x -> x ^ pow) +
            (sq y)
 
sq 0 = 0
sq x = x ^ pow
 
pow = 2
 