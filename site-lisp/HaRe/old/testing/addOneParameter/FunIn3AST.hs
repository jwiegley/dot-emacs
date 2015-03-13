module FunIn3 where
main :: Int
 
main
    =   let foo :: a -> Int -> Int
             
            foo y x
                = h + t
              where (h, t) = head $ (zip [1 .. x] [3 .. 15])
             
            foo_y = undefined
        in (let a = 10
                 
                b = 10
            in (((foo foo_y) 5) + a) + b)
 