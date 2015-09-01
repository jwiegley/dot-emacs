module FunIn1 where
foo :: Int
 
foo = h + t
  where (h, t) = head $ (zip [1 .. 7] [3 .. 15])
 
main :: Int
 
main = foo
 