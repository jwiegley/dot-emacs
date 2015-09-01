module TiFun where

-- Some tests to make sure that (->) a b = a->b and (,) a b = (a,b).

f :: (->) a a
f = id

pair :: a -> b -> (,) a b
pair x y = (x,y)
