module TupleIn1 where


f :: (a, ([Int],c)) -> ([Int],c)
f (x, y@([], m)) = y