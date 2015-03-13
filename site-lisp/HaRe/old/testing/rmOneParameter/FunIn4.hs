module FunIn4 where

--Any unused parameter to a definition can be removed.

--In this example: remove 'x' will fail, as (x,y) is treated as one parameter and 'y' is used.

foo (x,y)  = h + t where (h,t) = head $ zip [1..7] [3..y] 

main :: Int
main = foo (10, 20) 
 
