module FunIn5 where
foo :: a -> Int -> Int
 
foo h x
    = h + t
  where (h, t) = head $ (zip [1 .. x] [3 .. 15])
 
foo_h = undefined
 
main :: Int
 
main = (foo foo_h) 4
 