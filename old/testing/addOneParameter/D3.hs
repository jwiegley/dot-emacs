module D3(sumSquares) where

{- add parameter 'y' to 'sumSquares'. 'sumSquares_y_1' to be added to the 
   export list -}
 
sumSquares (x:xs) = sq x + sumSquares xs
sumSquares [] = 0

sq x = x ^ pow

pow =2 

