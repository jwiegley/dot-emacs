module D7 where

{- Rename 'fringe' to 'myFringe'. 
   This affects module 'D7' and 'C7'
-}
data Tree a = Leaf a | Branch (Tree a) (Tree a) 

fringe  :: Tree a -> [a]
fringe (Leaf x ) = [x]
fringe (Branch left right) = fringe left ++ fringe right
