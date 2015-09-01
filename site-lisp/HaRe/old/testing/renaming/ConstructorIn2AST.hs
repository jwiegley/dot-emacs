module ConstructorIn2 where
data BTree a
    = Empty | Tree a (BTree a) (BTree a) deriving Show
 
buildtree :: Ord a => [a] -> BTree a
 
buildtree [] = Empty
buildtree ((x : xs)) = insert x (buildtree xs)
 
insert :: Ord a => a -> (BTree a) -> BTree a
 
insert val Empty = Tree val Empty Empty
insert val tree@(Tree tval left right)
    | val > tval = Tree tval left (insert val right)
    | otherwise = Tree tval (insert val left) right
 
main :: BTree Int
 
main = buildtree [3, 1, 2]
 