module PatIn2 where
foo :: Int
 
foo = (h h_x) + t
  where
      (h, t) = head $ (zip [1 .. 10] [3 .. 15])
      h_x = undefined
 
main :: Int
 
main = foo
 