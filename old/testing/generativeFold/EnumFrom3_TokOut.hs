module EnumFrom3 where

{- map2 xs = map (+) [1 ..] -}

map2 xs = (case ((+), [1..2]) of
               (f, []) -> []
               (f, (x : xs)) -> (f x) : (map2 xs))

