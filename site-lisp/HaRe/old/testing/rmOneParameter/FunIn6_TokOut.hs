module FunIn6 where

--Any unused parameter to a definition can be removed.

--In this example: remove x. The brackets enclosing 'foo' will also be removed.

foo  = h + t where (h,t) = head $ zip [1..10] [3..10]
                      
main :: Int
main = foo + foo
 
