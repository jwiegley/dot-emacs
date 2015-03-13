module GuardIn1 where
sumSquares x y
    = (if x == 0 then 0 else x ^ pow) + (sq y)
 
sq x
    | x == 0 = 0
    | otherwise = x ^ pow
 
pow = 2
 