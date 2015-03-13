module B8 where


--Any type/data constructor name declared in this module can be renamed.
--Any type variable can be renamed.

--Rename type Constructor 'BTree' to 'MyBTree' 
data BTree a = Empty | T a (BTree a) (BTree a)
               deriving Show

buildtree :: (Monad m, Ord a) => [a] -> m (BTree a)
buildtree [] = return Empty
buildtree (x:xs) = do
                     res1 <- buildtree xs
                     res <- insert x res1
                     return res

insert :: (Monad m, Ord a) => a -> BTree a -> m (BTree a)
insert val1 t@(T val Empty Empty)
 | val1 == 42 = let val = 42 in t
 | otherwise = t


main :: IO ()
main = do
           (a, n@(T val Empty Empty)) <- buildtree [3, 1, 2]
           let val = 42
           putStrLn $ (show n)