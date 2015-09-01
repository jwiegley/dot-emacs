module FunIn6 where
main :: Int
 
main = (foo (h + t)) + 17
 
foo ht = ht + (snd tup)
 
tup@(h, t) = head $ (zip [1 .. 10] [3 .. 15])
 