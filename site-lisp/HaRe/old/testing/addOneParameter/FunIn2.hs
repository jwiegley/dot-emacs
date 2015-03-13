module FunIn2 where

--Default parameters can be added to definition of functions and simple constants.

--In this example: add parameter 'y' to 'foo'

main::Int->Int 
main =foo  where foo :: Int -> Int
                 foo_y_1 =15
                 foo x= h + t where (h,t) = head $ zip [1..x] [3..foo_y_1]   
                          