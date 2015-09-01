module TreeIn3 where

data Tree a = Leaf a | Branch (Tree a) (Tree a) 

fringe :: Tree a -> [a]
fringe (Leaf x) = [x]
fringe (Branch left right@(Leaf b_1))
    = (fringe left) ++ (fringe right)
fringe (Branch left right@(Branch b_1 b_2))
    =   case b_2 of
            b_2@(Leaf b_3) -> (fringe left) ++ (fringe right)
            b_2@(Branch b_4 b_3)
                -> (fringe left) ++ (fringe right)
fringe (Branch left right@(Branch b_1 b_2))
    = (fringe left) ++ (fringe right)
fringe (Branch left right)
    = (fringe left) ++ (fringe right)
