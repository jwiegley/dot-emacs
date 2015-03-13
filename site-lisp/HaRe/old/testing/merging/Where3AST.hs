module Where3 where
f3 l
    = (ls, res)
  where
      ls = take (rs - 1) l
      rs = length l
      res = length l
 
f1 :: [a] -> [a]
 
f1 l
    = ls
  where
      ls = take (rs - 1) l
      rs = length l
 
f2 :: [a] -> Int
 
f2 l = res where res = length l
 