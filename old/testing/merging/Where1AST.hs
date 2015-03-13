module Where1 where
f3 x
    = (ls, rs)
  where
      ls = x + 1
      rs = x - 1
 
f1 :: Int -> Int
 
f1 x = ls where ls = x + 1
 
f2 :: Int -> Int
 
f2 x = rs where rs = x - 1
 