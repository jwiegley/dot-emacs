module FunIn3 where
foo y
    = h + t where (h, t) = head $ (zip [1 .. 7] [3 .. y])
 
main :: Int
 
main = foo 20
 