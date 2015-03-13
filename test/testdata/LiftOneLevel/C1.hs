module LiftOneLevel.C1 where

import LiftOneLevel.D1 hiding (main)

sumSquares1 (x:xs) = sq x + sumSquares1 xs
 
sumSquares1 [] = 0
  
sq x =x ^pow

pow = 2

