module A3 where
data BTree a
    = Empty | T a (BTree a) (BTree a) deriving Show
 
buildtree :: Ord a => [a] -> BTree a
 
buildtree [] = Empty
buildtree ((x : xs)) = insert x (buildtree xs)
 
insert :: Ord a => a -> (BTree a) -> BTree a
 
insert val (t@(T val Empty Empty))
    = T val Empty result where result = t
insert val (T tval left right)
    | val > tval = T tval left (insert val right)
    | otherwise = T tval (insert val left) right
 
newPat_1 = Empty
 
main :: BTree Int
 
main = buildtree [3, 1, 2]
 