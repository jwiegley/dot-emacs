module FunIn5 where
foo = h + t
  where
      (h, t) = head $ (zip [1 .. a] [3 .. b])
      a = 10
      b = 17
 
main :: Int
 
main = foo
 