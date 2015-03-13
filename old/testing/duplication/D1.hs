module D1(sumSquares) where

{-Duplicate function 'sumSquares' with a new name 'anotherFun',
  This refactoring only affects the current module.-}

sumSquares (x:xs) = sq x + sumSquares xs
  where 
     sq x = x ^ pow
     pow =2 
 
sumSquares [] = 0





