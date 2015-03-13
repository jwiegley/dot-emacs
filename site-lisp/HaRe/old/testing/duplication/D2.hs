module D2 where

{-Duplicate function 'sumSquares' with a new name 'anotherFun',
  This refactoring affects modules 'D2','C2' and 'A2'-}

sumSquares (x:xs) = sq x + sumSquares xs
sumSquares [] = 0

sq x = x ^ pow

pow =2


