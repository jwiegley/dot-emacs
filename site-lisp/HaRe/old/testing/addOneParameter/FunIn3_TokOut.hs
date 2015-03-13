module FunIn3 where

--Default parameters can be added to definition of functions and simple constants.

--In this example: add parameter 'y' to 'foo'

main::Int
main =let foo :: a -> Int -> Int
          foo y  x= h + t 
               where (h,t) = head $ zip [1..x] [3..15]

          foo_y = undefined  in (let a=10
                                     b=10
                                 in (foo foo_y) 5+a+b)
