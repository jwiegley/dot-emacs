module D5 (sumFun, f, f_gen, y) where
y = 0
 
f z x = x + z
 
f_gen = (y + 1)
 
sumFun xs = sum $ (map (f (y + 1)) xs)
 