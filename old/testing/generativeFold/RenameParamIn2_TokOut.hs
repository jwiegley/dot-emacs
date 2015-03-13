module RenameParamIn2 where

{- add1 n xs = foldl (+) n xs -}

add1 n xs = (case ((+), n, xs) of
                 (f, z, []) -> z
                 (f, z, (x : xs)) -> add1 (  ((+) n x)) xs)


{- by the rule above:
     foldl f (f z x) xs = add1 (f z x) xs -}




