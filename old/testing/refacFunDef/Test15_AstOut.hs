module Test15 where
f n = n * (f (n - 1))
 
g = 13 * (f (13 - 1))
 