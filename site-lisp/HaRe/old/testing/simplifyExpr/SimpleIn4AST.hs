module SimpleIn4 where
f :: (Maybe a) -> a
 
f x@(Nothing)
    =   (case x of
             Nothing -> error "Maybe.fromJust: Nothing"
             (Just x) -> x)
f x@(Just y)
    =   (case x of
             Nothing -> error "Maybe.fromJust: Nothing"
             (Just x) -> x)
 
f_1 x@(Nothing)
    =   (case x of
             Nothing -> return 0
             (Just x) -> return 1)
 
fromJust :: (Maybe a) -> a
 
fromJust Nothing = error "Maybe.fromJust: Nothing"
fromJust (Just x) = x
 
g :: [Int] -> Int
 
g ((x : xs)) = x + (head (tail xs))
 