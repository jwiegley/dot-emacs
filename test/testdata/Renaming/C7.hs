module Renaming.C7(myFringe)  where 

import Renaming.D7

myFringe:: Tree a -> [a]
myFringe (Leaf x ) = [x]
myFringe (Branch left right) = myFringe left ++ fringe right




