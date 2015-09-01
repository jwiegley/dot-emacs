module B7(myFringe,sumSquares)where

import D7 
import C7 hiding (myFringe)

myFringe:: Tree a -> [a]
myFringe (Leaf x ) = [x]
myFringe (Branch left right) = myFringe right

sumSquares1 (x:xs)= x^2 + sumSquares xs
sumSquares1 [] =0 


  

