module B1 where

import A1

f :: C1 -> [Int]
f (C1 x@[]) = x
f (C1 x@(b_1 : b_2)) = x
f (C1 x) = x