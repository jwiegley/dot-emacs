module D1 where

{-add parameter 'f' to function  'sq' . This refactoring
  affects module 'D1', 'C1' and 'A1'-}

sumSquares (x:xs) = sq x + sumSquares xs
 
sumSquares [] = 0

sq x = x ^ pow

pow =2 

