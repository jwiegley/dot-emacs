module ListComp2 where

{- map2 xs = map length [ g | (Just g) <- xs ] -}

map2 xs = (case (length, [x | x <- xs]) of
               (f, []) -> []
               (f, (y : ys)) -> (f y) : (map f [j | (Just j) <- (y:ys)]))