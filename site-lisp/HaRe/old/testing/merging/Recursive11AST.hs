module Recursive11 where
f3 n l
    = (g1 n l, g n l)
  where
      g1 :: Int -> [a] -> [a]
      g1 n [] = []
      g1 0 xs = []
      g1 n ((x : xs)) = (x : ls) where ls = g1 (n - 1) xs
      g :: Int -> [a] -> [a]
      g n [] = []
      g 0 xs = xs
      g n ((x : xs)) = rs where rs = g (n - 1) xs
 
f1 :: Int -> [a] -> [a]
 
f1 n l
    = g1 n l
  where
      g1 :: Int -> [a] -> [a]
      g1 n [] = []
      g1 0 xs = []
      g1 n ((x : xs)) = (x : ls) where ls = g1 (n - 1) xs
 
f2 :: Int -> [a] -> [a]
 
f2 n l
    = g n l
  where
      g :: Int -> [a] -> [a]
      g n [] = []
      g 0 xs = xs
      g n ((x : xs)) = rs where rs = g (n - 1) xs
 