module L1 where


--Any type/data constructor name declared in this module can be renamed.
--Any type variable can be renamed.

--Rename type Constructor 'BTree' to 'MyBTree' 
data BTree a = Empty | T a (BTree a) (BTree a)
               deriving Show

buildtree :: Ord a => [a] -> (BTree a)
buildtree [] =  Empty
buildtree (x:xs) = head (insert x (buildtree xs))


insert ::  Ord a => a -> BTree a -> [BTree a]
insert val v2 = do
                  case v2 of
                   T val Empty Empty 
                                       | val == val -> [Empty]
                                       | otherwise -> [(T val Empty Empty), Empty] -- (T val Empty Empty))
                   T val (T val2 Empty Empty) Empty -> [Empty]
                   _ ->  [v2]


main :: IO ()
main = do
           let f = [ (T val Empty Empty) | (T val Empty Empty) <- insert 42
                                                     (buildtree [1, 2, 3])]
           if True 
              then do
                 putStrLn $ show 42
              else do
                 putStrLn $ show 42