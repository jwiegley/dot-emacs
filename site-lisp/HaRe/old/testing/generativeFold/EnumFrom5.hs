module EnumFrom5 where

{- map2 xs = map (+) [ 1 ,2 .. 5] -}

map2 xs = (case ((+), [1,2..5]) of
               (f, []) -> []
               (f, (x : xs)) -> (f x) : (map (+) [1,2 .. 5]))

