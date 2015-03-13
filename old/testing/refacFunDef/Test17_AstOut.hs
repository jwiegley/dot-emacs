module Test17 where
f ((x : xs)) (y, z) = (xs ++ [x]) ++ ([y] ++ z)
 
g = f (1 : [2, 3, 4]) (5, [6, 7])
 