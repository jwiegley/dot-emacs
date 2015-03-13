module FunIn3 where

--Any unused parameter to a definition can be removed.

--In this example: remove the parameter 'x' (or 'z') to 'foo'

foo z@x y  = h + t where (h,t) = head $ zip [1..7] [3..y] 

main :: Int
main = foo 10 20 
 
