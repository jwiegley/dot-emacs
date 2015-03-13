module TupleIn1 where
f :: (a, ([Int], c)) -> ([Int], c)
 
f (x, y@([], m))
    =   case y of
            y@(b_1, b_2) -> y
f (x, y@([], m)) = y
 