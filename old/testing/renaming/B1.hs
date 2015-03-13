module B1 (myFringe)where

import D1 hiding (sumSquares)

import qualified D1 

instance SameOrNot Float where
   isSame a  b = a ==b
   isNotSame a b = a /=b

myFringe:: Tree a -> [a]
myFringe (Leaf x ) = [x]
myFringe (Branch left right) = myFringe right

sumSquares (x:xs)= x^2 + sumSquares xs
sumSquares [] =0 


  

