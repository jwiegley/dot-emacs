module B4 (myFringe)where

import D4 hiding (sumSquares, fringe)
import D4 (fringe)
import C4 hiding (myFringe)

myFringe:: Tree a -> [a]
myFringe (Leaf x ) = [x]
myFringe (Branch left right) = myFringe right

sumSquares (x:xs)= x^2 + sumSquares xs
sumSquares [] =0 


  

