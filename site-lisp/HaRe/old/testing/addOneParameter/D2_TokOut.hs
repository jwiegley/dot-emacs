module D2 where

{-add parameter 'f' to function  'sq' . This refactoring
  affects module 'D2', 'C2' and 'A2'. It aims to test the
  creating of default parameter name.-}

sumSquares (x:xs) = (sq sq_f) x + sumSquares xs
 
sumSquares [] = 0

sq f x = x ^ pow

sq_f = undefined

pow =2 

