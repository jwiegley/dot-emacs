module D1 where

{-remove parameter 'ys' from function 'sumSquares'. This refactoring
  affects module 'D1', and 'A1'-}

sumSquares (x:xs) ys = sq x + sumSquares xs xs
 
sumSquares [] ys = 0

sq x = x ^ pow

pow =2 

