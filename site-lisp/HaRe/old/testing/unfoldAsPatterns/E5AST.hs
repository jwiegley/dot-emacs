module E5 where
data BTree a
    = Empty | T a (BTree a) (BTree a) deriving Show
 
buildtree :: Ord a => [a] -> BTree a
 
buildtree [] = Empty
buildtree ((x : xs)) = head (insert x (buildtree xs))
 
insert :: Ord a => a -> (BTree a) -> [BTree a]
 
insert val v2
    =   do case v2 of
               T val Empty Empty
                   | val == val -> [Empty]
                   | otherwise -> [(T val Empty Empty), Empty]
               T val (T val2 Empty Empty) Empty -> [Empty]
               _ -> [v2]
 
main :: IO ()
 
main
    =   do let f   =   [(T a_1 Empty Empty) | n@(T a_1
                                                   Empty Empty) <- insert 42
                                                                       (buildtree
                                                                            [1,
                                                                             2,
                                                                             3])]
           if True
             then do putStrLn $ (show 42)
             else do putStrLn $ (show 42)
 