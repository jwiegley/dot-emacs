module Demote.D3(sumSquares) where

--demote  'sumSquares' should fail as it is explicitly exported.

sumSquares (x:xs) = sq x + sumSquares xs
sumSquares [] = 0

sq x = x ^pow 

pow = 2

main = sumSquares [1..4]

