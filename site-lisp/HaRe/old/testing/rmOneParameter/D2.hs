module D2 where

{-remove parameter 'ys' from function 'sumSquares'. This refactoring
  affects module 'D1', and 'A1'. This aims to test removing a  
  parameter from a recursion function-}

sumSquares (x:xs) ys = sq x + sumSquares xs ys
 
sumSquares [] ys = 0

sq x = x ^ pow

pow =2 

