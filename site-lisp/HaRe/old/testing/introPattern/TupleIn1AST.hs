module TupleIn1 where
f :: (a, b) -> a
 
f x@((,) b_1 b_2) = fst x
f x = fst x
 