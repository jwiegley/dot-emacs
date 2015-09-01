module RenameParamIn3 where


{- de xs = deleteBy (==) 0 xs -}

de xs = (case ((==), 0, xs) of
             (_, _, []) -> []
             (eq, x, (y : ys))
                 -> if x `eq` y then ys else y : (deleteBy eq x ys)) 


{- uses equation that de xs = deleteBy (==) 0 xs -}


-- | The 'deleteBy' function behaves like 'delete', but takes a
-- user-supplied equality predicate.
deleteBy                :: (a -> a -> Bool) -> a -> [a] -> [a]
deleteBy _  _ []        = []
deleteBy eq x (y:ys)    = if x `eq` y then ys else y : deleteBy eq x ys