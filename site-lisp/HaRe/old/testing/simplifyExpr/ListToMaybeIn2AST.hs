module ListToMaybeIn2 where
f :: [a] -> Maybe a
 
f x@[]
    =   (case x of
             [] -> Nothing
             (a : _) -> Just a)
f x@((b_1 : b_2))
    =   (case x of
             [] -> Nothing
             (a : _) -> Just a)
f x = listToMaybe x
 
f_1 x@((b_1 : b_2))
    =   (case x of
             [] -> return 0
             (a : _) -> return 1)
 
listToMaybe :: [a] -> Maybe a
 
listToMaybe [] = Nothing
listToMaybe ((a : _)) = Just a
 
g :: [Int] -> Int
 
g ((x : xs)) = x + (head (tail xs))
 