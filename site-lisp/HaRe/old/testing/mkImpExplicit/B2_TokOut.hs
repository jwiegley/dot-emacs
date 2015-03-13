
-- In this example, make the used items explicit in 'import C1 ...'.

module B2 (myFringe)where

import D1 hiding (sumSquares, fringe)
import D1 (fringe)
import C1 (Tree(Leaf, Branch))

myFringe:: Tree a -> [a]
myFringe (Leaf x ) = [x]
myFringe (Branch left right) = myFringe right

sumSquares (x:xs)= x^2 + sumSquares xs
sumSquares [] =0 


  

