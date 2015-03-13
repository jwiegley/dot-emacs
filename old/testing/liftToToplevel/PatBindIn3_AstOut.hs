module PatBindIn3 where
sumSquares x = (sq x pow) + (sq x pow) where pow = 2
 
sq x pow = x ^ pow
 
anotherFun 0 y = sq y where sq x = x ^ 2
 