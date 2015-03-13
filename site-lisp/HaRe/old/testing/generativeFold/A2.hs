module A2 where

len xs = length xs

{- map2 xs = map len xs -}

map2 xs = case (len, xs) of
               (f, []) -> []
               (f, (x : xs)) -> (f x) : (map f xs)



