module B2 (myFringe)where

import D2 hiding (sumSquares, fringe)
import D2 (fringe)
import C2 hiding (myFringe)

myFringe:: Tree a -> [a]
myFringe (Leaf x ) = [x]
myFringe (Branch left right) = myFringe right

sumSquares (x:xs)= x^2 + sumSquares xs
sumSquares [] =0 


  

