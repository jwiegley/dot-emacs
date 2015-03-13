module FunIn5 where

--Any unused parameter to a definition can be removed.

--In this example: remove (x,y) (stop the cursor at 'x' or 'y') 

foo   = h + t where (h,t) = head $ zip [1..a] [3..b]
                    a=10
                    b=17 

main :: Int
main = foo  
 
