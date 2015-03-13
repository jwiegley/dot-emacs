module Test16 where
f (x, y) = (x ++ [y]) ++ x
 
g = f ([1, 2, 3], [1, 2, 2], 2)
 