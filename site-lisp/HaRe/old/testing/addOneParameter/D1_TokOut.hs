module D1 where

{-add parameter 'f' to function  'sq' . This refactoring
  affects module 'D1', 'C1' and 'A1'-}

sumSquares (x:xs) = (sq sq_f) x + sumSquares xs
 
sumSquares [] = 0

sq f x = x ^ pow

sq_f = undefined

pow =2 

