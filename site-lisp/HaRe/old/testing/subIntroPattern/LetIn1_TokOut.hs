module LetIn1 where

data Tree a = Leaf a | Branch (Tree a) (Tree a) 


fringe_global x  = let
                      fringe :: Tree a -> [a]
                      fringe (Leaf x) = [x]
                      fringe (Branch left@(Leaf b_1) right)
                          = (fringe left) ++ (fringe right)
                      fringe (Branch left@(Branch b_1 b_2) right)
                          = (fringe left) ++ (fringe right)
                      fringe (Branch left right)
                          = (fringe left) ++ (fringe right)
                   in fringe x