module TupleIn2 where


f :: (a, ([Int],c)) -> ([Int],c)
f (x, y@(b_1@[], b_2)) = y
f (x, y@(b_1@(b_4 : b_3), b_2)) = y
f (x, y@(b_1, b_2)) = y
f (x, y@([], m)) = y