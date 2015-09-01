module A2 where

import C2 

main xs = case xs of 
             [] -> 0
             [x:xs] -> x^pow + sumSquares xs

