module TupleIn1 where

{- partition p xs = foldr (select p) ([], []) xs -}

partition p xs = (case ((select p), ([],[]), xs) of
                      (f, z, []) -> z
                      (f, z, (x : xs)) -> f x (foldr f z xs))


{- partition p xs = foldr f z xs where f = select p -}


select p x ~(ts,fs) | p x       = (x:ts,fs)
                    | otherwise = (ts, x:fs)

de xs = deleteBy (==) 0 xs

deleteBy _  _ []        = []
deleteBy eq x (y:ys)    = if x `eq` y then ys else y : deleteBy eq x ys
