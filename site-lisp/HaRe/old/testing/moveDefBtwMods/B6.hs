module B6(myFringe,sumSquares)where

import D6 
import C6 hiding (myFringe)

myFringe:: Tree a -> [a]
myFringe (Leaf x ) = [x]
myFringe (Branch left right) = myFringe right

sumSquares1 (x:xs)= x^2 + sumSquares xs
sumSquares1 [] =0 


  

