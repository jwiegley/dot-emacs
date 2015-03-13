module Renaming.C1  where 

import Renaming.D1

instance SameOrNot Double where
   isSame a  b = a ==b
   isNotSame a b = a /=b

myFringe:: Tree a -> [a]
myFringe (Leaf x ) = [x]
myFringe (Branch left right) = myFringe left 




