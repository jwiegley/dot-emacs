module Guards2 where

g1 :: Int -> String -> String
g1 n [] = []
g1 n (x:xs)
 | n == 0 = ""
 | otherwise = x :ls
              where
               ls = g1 (n-1) xs


g2 :: Int -> String -> String
g2 n [] = []
g2 n (x:xs)
 | n == 1 = xs
 | otherwise = rs
                where
                 rs = g2 (n-1) xs

 
