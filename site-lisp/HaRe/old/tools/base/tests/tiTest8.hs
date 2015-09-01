module Prelude where

data Bool = False | True

not False = True
not True = False

data [] a = [] | a : [a]

map f [] = []
map f (x:xs) = f x:map f xs

null [] = True
null _ = False

--b::Bool
b = null []

id = \ x -> x

const x y = let z = False in x

type B = Bool
