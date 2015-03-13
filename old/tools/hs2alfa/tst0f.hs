module Prelude where

data [] a = [] | a : [a]

map f [] = []
map f (x:xs) = f x:map f xs

class Functor f where fmap :: (a->b)->f a->f b

instance Functor [] where fmap = map

