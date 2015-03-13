module D3 where


--Any type/data constructor name declared in this module can be renamed.
--Any type variable can be renamed.

--Rename type Constructor 'BTree' to 'MyBTree' 
data BTree a = Empty | T a (BTree a) (BTree a)
               deriving Show

buildtree :: Ord a => [a] -> BTree a
buildtree [] = Empty
buildtree (x:xs) = insert x (buildtree xs)

insert :: Ord a => a -> BTree a -> BTree a
insert val v2 = let f (new@(T val Empty Empty)) = new 
                         in f (res v2)
                           where 
                             res (T val Empty Empty) = T val Empty Empty

newPat_1 = Empty


f :: String -> String
f newPat_2@((x : xs)) = newPat_2

main :: BTree Int
main = buildtree [3,1,2] 