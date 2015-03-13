module Lambda1 where

{- map2 xs = map (\ ((y:ys)) -> y) xs-}

map2 xs = (case ((\ ((y : ys)) -> y), xs) of
               (f, []) -> []
               (f, (x : xs)) -> (f x) : (map2 xs))