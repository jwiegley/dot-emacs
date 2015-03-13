module LetIn1 where

data Tree a = Leaf a | Branch (Tree a) (Tree a) 


fringe_global x  = let
                      fringe :: Tree a -> [a]
                      fringe (Leaf x ) = [x]
                      fringe (Branch left right) = fringe left ++ fringe right
                   in fringe x