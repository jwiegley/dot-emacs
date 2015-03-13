module PatIn1 where
foo :: a -> Int
 
foo x
    = h + t
  where (h, t) = head $ (zip [1 .. 10] [3 .. 15])
 
foo_x = undefined
 
main :: Int
 
main = (foo foo_x)
 