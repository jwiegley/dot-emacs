
{- Refactoring: move the definiton 'fringe' to module C1. This example aims
   to test the moving of the definition and the modification of export/import -}

module D1(fringe, sumSquares) where

import C1

fringe :: Tree a -> [a]
fringe p |isLeaf p
         = [(leaf1 p)]
fringe p |isBranch p
         = fringe (branch1 p) ++ fringe (branch2 p)                
   
sumSquares (x:xs) = sq x + sumSquares xs
sumSquares [] = 0
   
sq x = x ^pow 

pow = 2




