module LiftOneLevel.D3 where

{-lift 'sq' to top level. This refactoring only affects the
current module. -}
 
sumSquares (x:xs) = sq x + sumSquares xs
  where
     sq x = x ^ pow

sumSquares [] = 0

pow = 2

