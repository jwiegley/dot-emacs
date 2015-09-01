module FunIn2 where
inc :: Int -> Int
 
foo :: Int
 
foo = h + t
  where (h, t) = head $ (zip [1 .. 7] [3 .. 15])
 
inc x = x + 1
 
main :: Int
 
main = foo
 