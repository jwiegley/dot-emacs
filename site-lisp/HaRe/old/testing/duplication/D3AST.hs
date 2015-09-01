module D3 where
sumSquares ((x : xs)) = (sq x) + (sumSquares xs)
sumSquares [] = 0
 
anotherFun ((x : xs)) = (sq x) + (anotherFun xs)
anotherFun [] = 0
 
sq x = x ^ pow
 
pow = 2
 