module A3 where


--Any type/data constructor name declared in this module can be renamed.
--Any type variable can be renamed.

--Rename type Constructor 'BTree' to 'MyBTree' 
data BTree a = Empty | T a (BTree a) (BTree a)
               deriving Show

buildtree :: Ord a => [a] -> BTree a
buildtree [] = Empty
buildtree (x:xs) = insert x (buildtree xs)

insert :: Ord a => a -> BTree a -> BTree a
insert val (T val Empty Empty) = T val Empty result
                    where
                       result = T val Empty Empty
insert val (T tval left right)
   | val > tval = T tval left (insert val right)
   | otherwise = T tval (insert val left) right
       
newPat_1 = Empty


main :: BTree Int
main = buildtree [3,1,2] 
