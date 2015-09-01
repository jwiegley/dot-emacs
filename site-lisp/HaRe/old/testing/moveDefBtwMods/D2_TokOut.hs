
{- Refactoring: move the definiton 'fringe' to module B2 which is a client module of 
   D2. This example aims to test the moving of the definition and the modification 
   of export/import -}

module D2(sumSquares) where

import C2


   
sumSquares (x:xs) = sq x + sumSquares xs
sumSquares [] = 0
   
sq x = x ^pow 

pow = 2




