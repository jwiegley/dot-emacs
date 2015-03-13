module GuardsIn3 where


f x@1 y@(z:zs) 
 | x == 1 = (z : [1, 2])
 | otherwise = [1,2]


