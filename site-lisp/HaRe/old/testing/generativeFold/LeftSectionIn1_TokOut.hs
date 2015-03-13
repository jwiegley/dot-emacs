module LeftSectionIn1 where

{- map2 xs = map (+ 1) xs -}

map2 xs = (case ((+ 1), xs) of
               (f, []) -> []
               (f, (x : xs)) -> (f x) : (map2 xs))

