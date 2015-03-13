
{- Refactoring: move the definiton 'fringe' to module C1. This example aims
   to test the moving of the definition and the modification of export/import -}

module D3(myFringe,fringe, sumSquares) where

import C3

myFringe:: Tree a -> [a]
myFringe (Leaf x ) = [x]
myFringe (Branch left right) = myFringe left 

fringe :: Tree a -> [a]
fringe (Leaf x) = [x]
fringe (Branch left right) = fringe left ++ fringe right                
   
sumSquares (x:xs) = sq x + sumSquares xs
sumSquares [] = 0
   
sq x = x ^pow 

pow = 2




