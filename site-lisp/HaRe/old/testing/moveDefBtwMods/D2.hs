
{- Refactoring: move the definiton 'fringe' to module B2 which is a client module of 
   D2. This example aims to test the moving of the definition and the modification 
   of export/import -}

module D2(fringe, sumSquares) where

import C2

fringe :: Tree a -> [a]
fringe (Leaf x) = [x]
fringe (Branch left right) = fringe left ++ fringe right                
   
sumSquares (x:xs) = sq x + sumSquares xs
sumSquares [] = 0
   
sq x = x ^pow 

pow = 2




