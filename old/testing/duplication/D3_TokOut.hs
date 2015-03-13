module D3 where

{-Duplicate function 'sumSquares' with a new name 'anotherFun',
  This refactoring affects modules 'D3' and 'C3'-}

sumSquares (x:xs) = sq x + sumSquares xs
sumSquares [] = 0

anotherFun (x:xs) = sq x + anotherFun xs
anotherFun [] = 0

sq x = x ^ pow

pow =2


