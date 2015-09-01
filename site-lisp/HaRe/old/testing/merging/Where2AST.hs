module Where2 where
g x l_1 l
    = (ls, rs)
  where
      ls = take x l_1
      rs = length l
 
f1 :: Int -> [a] -> [a]
 
f1 x l = ls where ls = take x l
 
f2 :: [a] -> Int
 
f2 l = rs where rs = length l
 