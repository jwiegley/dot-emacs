module MaybeIn1 where
f x@((y : ys))
    =   case x of
            [] -> Nothing
            (x : xs) -> Just x
 
f_1 x@((y : ys))
    =   case x of
            [] -> return 0
            (x : xs) -> return 1
 