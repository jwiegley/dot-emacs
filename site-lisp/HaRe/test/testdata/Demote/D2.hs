module Demote.D2 where

--demote  'sumSquares' should fail as it used by module 'A2'.

sumSquares (x:xs) = sq x + sumSquares xs
sumSquares [] = 0

sq x = x ^pow 

pow = 2

main = sumSquares [1..4]

