module A8 where
data BTree a
    = Empty | T a (BTree a) (BTree a) deriving Show
 
buildtree :: Ord a => [a] -> BTree a
 
buildtree [] = Empty
buildtree ((x : xs)) = snd (insert x (buildtree xs))
 
insert :: Ord a => a -> (BTree a) -> (Int, BTree a)
 
insert val (t@(T val1 Empty Empty)) = (42, t)
 
newPat_1 = Empty
 
f :: String -> String
 
f newPat_2@((x : xs)) = newPat_2
 
main :: BTree Int
 
main = buildtree [3, 1, 2]
 