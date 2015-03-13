module FunIn5 where

--Default parameters can be added to definition of functions and simple constants.

--In this example: add parameter 'h' to 'foo' will fail because of name clash.

foo :: Int -> Int
foo x= h + t where (h,t) = head $ zip [1..x] [3..15] 

main :: Int
main = foo 4
 