module FunIn1 where

--Any unused parameter to a definition can be removed.

--In this example: remove the parameter 'x' to 'foo'

foo :: Int -> Int
foo x= h + t where (h,t) = head $ zip [1..7] [3..15] 

main :: Int
main = foo 4
 