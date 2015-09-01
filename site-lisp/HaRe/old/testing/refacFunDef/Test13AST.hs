module Test13 where
f ((x : xs)) = x : xs
 
g = f (1 : [1, 2])
 