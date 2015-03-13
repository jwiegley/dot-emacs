
{- Refactoring: move the definiton 'fringe' to module C1. This example aims
   to test the moving of the definition and the modification of export/import -}

module D(fringe, sumSquares) where

import C

fringe :: Tree a -> [a]
fringe (Leaf x) = [x]
fringe (Branch left right) = fringe left ++ fringe right                
   
sumSquares (x:xs) = sq x + sumSquares xs
sumSquares [] = 0
   
sq x = x ^pow 

pow = 2




