module FunIn1 where
foo :: a -> Int -> Int
 
foo y x
    = h + t
  where (h, t) = head $ (zip [1 .. x] [3 .. 15])
 
foo_y = undefined
 
main :: Int
 
main = (foo foo_y) 4
 