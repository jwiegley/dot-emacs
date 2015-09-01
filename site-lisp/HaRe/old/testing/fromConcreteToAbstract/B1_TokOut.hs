module B1 (myFringe)where

import D1 hiding (sumSquares, fringe)
import D1 (fringe)
import C1 (Tree,leaf1,branch1,branch2,isLeaf,isBranch,mkLeaf,mkBranch)

myFringe:: Tree a -> [a]
myFringe p |isLeaf p
           = [(leaf1 p)]
myFringe p |isBranch p
           = myFringe (branch2 p)

sumSquares (x:xs)= x^2 + sumSquares xs
sumSquares [] =0 


  

