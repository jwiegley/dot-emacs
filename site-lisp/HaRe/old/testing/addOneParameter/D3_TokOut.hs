module D3(sumSquares,sumSquares_y) where

{- add parameter 'y' to 'sumSquares'. 'sumSquares_y_1' to be added to the 
   export list -}
 
sumSquares y (x:xs) = sq x + (sumSquares y) xs
sumSquares y [] = 0

sumSquares_y = undefined

sq x = x ^ pow

pow =2 

