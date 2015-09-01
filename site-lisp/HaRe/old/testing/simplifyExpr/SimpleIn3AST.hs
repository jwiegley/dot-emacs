module SimpleIn3 where
f :: (Maybe a) -> a
 
f x@(Just y)
    =   (case x of
             Nothing -> error "Maybe.fromJust: Nothing"
             (Just x) -> x)
 
f_1 x@(Just y)
    =   (case x of
             Nothing -> return 0
             (Just x) -> return 1)
 
fromJust :: (Maybe a) -> a
 
fromJust Nothing = error "Maybe.fromJust: Nothing"
fromJust (Just x) = x
 
g :: [Int] -> Int
 
g ((x : xs)) = x + (head (tail xs))
 