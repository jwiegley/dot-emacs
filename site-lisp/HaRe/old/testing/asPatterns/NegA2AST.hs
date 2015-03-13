module NegA2 where
data BTree a
    = Empty | T a (BTree a) (BTree a) deriving Show
 
buildtree :: Ord a => [a] -> BTree a
 
buildtree [] = Empty
buildtree ((x : xs)) = n x (buildtree xs)
 
n :: Ord a => a -> (BTree a) -> BTree a
 
n val Empty = T val Empty Empty
n val (T tval left right)
    | val > tval = T tval left (n val right)
    | otherwise = T tval (n val left) right
 
main :: BTree Int
 
main = buildtree [3, 1, 2]
 