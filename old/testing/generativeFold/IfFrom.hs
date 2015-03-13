module IfFrom where

{- map2 xs = map (if xs == [] then (+) else (-)) [ 1 ,2 .. 5] -}

map2 xs = (case ((+), [1,2..5]) of
               (f, []) -> []
               (f, (x : xs)) -> (f x) : (map (if xs == [] then (+) else (-))
                                             [1,2 .. 5]))

