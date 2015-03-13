module FunIn0 where

--Any unused parameter to a definition can be removed.

--To select a formal parameter, just need to stop the cursor at any position between the start 
--end position of this formal paramter.

--In this example, remove '[x,y]'

foo [x,y]= h + t where (h,t) = head $ zip [1..10] [3..10]
                      
main :: Int
main = foo [4,5]
 
