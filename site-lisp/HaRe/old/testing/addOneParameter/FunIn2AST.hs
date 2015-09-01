module FunIn2 where
main :: Int -> Int
 
main
    = (foo foo_y)
  where
      foo :: a -> Int -> Int
      foo_y_1 = 15
      foo y x
          = h + t
        where (h, t) = head $ (zip [1 .. x] [3 .. foo_y_1])
      foo_y = undefined
 