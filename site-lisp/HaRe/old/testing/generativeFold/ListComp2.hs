module ListComp2 where

{- map2 xs = map length [ x | x <- xs ] -}

map2 xs = (case (length, [x | x <- xs]) of
               (f, []) -> []
               (f, (y : ys)) -> (f y) : (map f [j | j <- ys]))