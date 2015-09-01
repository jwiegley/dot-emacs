module ConstructorIn1 where
data MyBTree a
    = Empty | T a (MyBTree a) (MyBTree a) deriving Show
 
buildtree :: Ord a => [a] -> MyBTree a
 
buildtree [] = Empty
buildtree ((x : xs)) = insert x (buildtree xs)
 
insert :: Ord a => a -> (MyBTree a) -> MyBTree a
 
insert val Empty = T val Empty Empty
insert val tree@(T tval left right)
    | val > tval = T tval left (insert val right)
    | otherwise = T tval (insert val left) right
 
main :: MyBTree Int
 
main = buildtree [3, 1, 2]
 