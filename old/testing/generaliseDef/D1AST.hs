module D1 (sumFun) where
y = 0
 
f z x = x + z
 
sumFun xs = sum $ (map (f (y + 1)) xs)
 