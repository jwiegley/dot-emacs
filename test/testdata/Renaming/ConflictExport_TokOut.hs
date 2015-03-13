module ConflictExport (D6.fringe, myFringe) where

{-Rename 'myFringe' to 'fringe' will fail because of
  conflicting exports. -}
import D6

myFringe:: Tree a -> [a]
myFringe (Leaf x ) = [x]
myFringe (Branch left right) = myFringe right




  

