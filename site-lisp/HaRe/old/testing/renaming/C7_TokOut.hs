module C7(C7.myFringe)  where 

import D7

myFringe:: Tree a -> [a]
myFringe (Leaf x ) = [x]
myFringe (Branch left right) = C7.myFringe left ++ D7.myFringe right




