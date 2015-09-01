
-- In this example, the first import declaration should be removed.
module B3 (myFringe)where

import C1 (Tree(Leaf,Branch))

myFringe:: Tree a -> [a]
myFringe (Leaf x ) = [x]
myFringe (Branch left right) = myFringe right

sumSquares (x:xs)= x^2 + sumSquares xs
sumSquares [] =0 


  

