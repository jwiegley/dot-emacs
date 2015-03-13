module FunIn2 where

--Any unused parameter to a definition can be removed.

--In this example: remove the parameter 'x' to 'foo'

foo,inc :: Int -> Int
foo x= h + t where (h,t) = head $ zip [1..7] [3..15] 

inc x=x+1

main :: Int
main = foo 4
 