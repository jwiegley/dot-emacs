module Recursive99 where
g _ "" = ("", "")
g 0 xs = ("", xs)
g n ((x : xs))
    = ((x : ls), rs)
  where
      ls = fst $ (g (n - 1) xs)
      rs = snd $ (g (n - 1) xs)
 
f1 :: Int -> String -> String
 
f1 _ "" = ""
f1 0 xs = ""
f1 n ((x : xs)) = (x : ls) where ls = f1 (n - 1) xs
 
f2 :: Int -> String -> String
 
f2 _ "" = ""
f2 0 xs = xs
f2 n ((x : xs)) = rs where rs = f2 (n - 1) xs
 