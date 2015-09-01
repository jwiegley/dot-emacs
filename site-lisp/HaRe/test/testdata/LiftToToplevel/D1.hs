module LiftToToplevel.D1 where

{-lift 'sq' to top level. This refactoring
  affects module 'D1' and 'C1' -}

sumSquares (x:xs) = sq x + sumSquares xs
  where 
     sq x = x ^ pow
     pow =2 
 
sumSquares [] = 0

main = sumSquares [1..4]


