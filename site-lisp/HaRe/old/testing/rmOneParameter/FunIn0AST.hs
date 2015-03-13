module FunIn0 where
foo = h + t
  where (h, t) = head $ (zip [1 .. 10] [3 .. 10])
 
main :: Int
 
main = foo
 