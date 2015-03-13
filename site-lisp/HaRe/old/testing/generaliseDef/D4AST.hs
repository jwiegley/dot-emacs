module D4 where
y = 0
 
f z x = x + (y + z)
 
sumFun xs = sum $ (map (f 1) xs)
 