module EnumFrom2 where

{- map2 xs = map (+) [1 .. 2] -}

map2 xs = (case ((+), [1..2]) of
               (f, []) -> []
               (f, (x : xs)) -> (f x) : (map2 xs))

