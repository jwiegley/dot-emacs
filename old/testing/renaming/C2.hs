module C2  where 

import D2

instance SameOrNot Double where
   isSame a  b = a ==b
   isNotSame a b = a /=b

myFringe:: Tree a -> [a]
myFringe (Leaf x ) = [x]
myFringe (Branch left right) = myFringe left 




