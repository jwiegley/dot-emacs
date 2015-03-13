module D2 where

sumSquares (x:xs) = sq x + sumSquares xs
sumSquares []     = 0

sq x = x ^ pow

pow =2 

main = sumSquares [1..4]


