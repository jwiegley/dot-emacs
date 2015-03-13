module SimpleIn3 where


f :: Maybe a -> a
f x@(Just y) = (case x of
                    Nothing -> error "Maybe.fromJust: Nothing"
                    (Just x) -> x)

-- | The 'fromJust' function extracts the element out of a 'Just' and
-- throws an error if its argument is 'Nothing'.
fromJust          :: Maybe a -> a
fromJust Nothing  = error "Maybe.fromJust: Nothing" -- yuck
fromJust (Just x) = x

g :: [Int] -> Int
g (x:xs) = x + head ( tail xs)

