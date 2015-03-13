module TupleIn2 where

-- test for longer length tuples


f :: (a,b,c,d,e,f,g) -> a
f x@(b_1, b_2, b_3, b_4, b_5, b_6, b_7) = fst x
f x = fst x