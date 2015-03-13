module C4  where 

import D4

instance SameOrNot Double where
   isSameOrNot a  b = a ==b
   isNotSame a b = a /=b

myFringe:: Tree a -> [a]
myFringe (Leaf x ) = [x]
myFringe (Branch left right) = myFringe left 




