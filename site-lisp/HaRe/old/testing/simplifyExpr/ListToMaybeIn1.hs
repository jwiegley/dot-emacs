module ListToMaybeIn1 where


f :: [a] -> Maybe a
f x@[] = (case x of
              [] -> Nothing
              (a : _) -> Just a)
f x@(b_1 : b_2) = listToMaybe x
-- f x = listToMaybe x

-- | The 'listToMaybe' function returns 'Nothing' on an empty list
-- or @'Just' a@ where @a@ is the first element of the list.
listToMaybe           :: [a] -> Maybe a
listToMaybe []        =  Nothing
listToMaybe (a:_)     =  Just a

g :: [Int] -> Int
g (x:xs) = x + head ( tail xs)

