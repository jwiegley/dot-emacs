module Prelude where

data Bool = False | True
data Int
data Maybe a = Nothing | Just a
data (,) a b = (,) a b

not False = True
not True = False

data [] a = [] | a : [a]

map f [] = []
map f (x:xs) = f x:map f xs

null = f
  where
    f [] = True
    f _ = False

t = null []
f = not t

{-
data P = P { x,y::Int }


origin P{x=0,y=0} = True
origin _ = False
-}

class Functor f where
  fmap :: (a->b) -> f a -> f b

instance Functor [] where fmap = map

ys = fmap id []

(id,const)  = (\x->x,\x y->x)

error s = undefined
undefined | False = undefined
