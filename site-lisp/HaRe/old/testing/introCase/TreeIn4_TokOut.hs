module TreeIn4 where

data Tree a = Leaf a | Branch (Tree a) (Tree a) 

fringe :: Tree a -> [a]
fringe (Leaf x) = [x]
fringe (Branch left right@(Leaf b_1))
    = (fringe left) ++ (fringe right)
fringe (Branch left right@(Branch b_1 b_2))
    = (fringe left) ++ (fringe right)
fringe (Branch left right)
    = (fringe left) ++ (fringe right)
