module Guards3 where


{- g3 :: Num a  => a  ->  [Char]  ->  ([Char], [Char] ) -}
g3 n [] = ([], [])
g3 n ((x : xs))
    | n == 0 = ("", xs)
    | otherwise = (x : (ls n ), (rs n ))
  where
      ls n = fst $ g3 (n - 1) xs
      rs n = snd $ g3 (n - 1) xs

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
 | n == 0 = xs
 | otherwise = rs
                where
                 rs = g2 (n-1) xs

 