module RenameParamIn1 where

{- map2 xs = map length xs -}

map2 xs@(l:ls) = case (length, xs) of
                   (f, []) -> []
                   (f, (l : ls)) -> (f l) : (map2 ls)

{- map f ls = map2 ls -}

