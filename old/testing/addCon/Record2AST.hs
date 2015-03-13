module Record2 where
data C a = F {f44 :: a, f1, f2 :: Int, f3 :: Bool}
 
g = f1 (F 1 2 True)
 