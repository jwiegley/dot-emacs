module Test17 where

f (x:xs) (y,z) = xs ++ [x] ++ ( [y] ++ z )

g = [2,3,4] ++ [1] ++ ( [5] ++ [6,7] )