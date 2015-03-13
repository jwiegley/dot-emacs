module WithLocalDeclIn2 where
sumSquares x y = (let pow = 2 in x ^ pow) + (sq y)
 
sq x = x ^ pow where pow = 2
 