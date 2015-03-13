module MaybeIn1 where



f x@(y:ys) = case x of
             [] -> Nothing
             (x:xs) -> Just x