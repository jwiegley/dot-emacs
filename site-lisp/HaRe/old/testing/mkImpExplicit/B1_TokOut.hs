
-- In this example, make the used items explicit in the first import decl.

module B1 (myFringe)where

import D1 ()
import D1 (fringe)
import C1 hiding (myFringe)

myFringe:: Tree a -> [a]
myFringe (Leaf x ) = [x]
myFringe (Branch left right) = myFringe right

sumSquares (x:xs)= x^2 + sumSquares xs
sumSquares [] =0 


  

