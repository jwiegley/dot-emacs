module SimpleIn1Az where

import Prelude


f x@[] = case x of
            []     -> error "head:empty list"
            (x:xs) -> x
f x = head x

f_1 x@[]
    =   case x of
            [] -> 0
            (x : xs) -> 1

g :: [Int] -> Int
g (x:xs) = x + head ( tail xs)

