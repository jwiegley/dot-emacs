module CaseIn2 where

--A new definition can be introduced to denote an identified sub-expression.
--The newly introduced definition may be a function binding
--or a simple constant binding. The new binding will be put at the end of the 
--local 'where' or 'let' clause depending on the scope of high lighted source.

--In this example: Introduce a new definition to denote 'y+1'
--this example aims to test introducing a function defintion instead of a constant.


foo::Int->Int
foo x= case x of
            1 -> foo 0
            0 ->((\a b c->addThree a b c) 1 2 3)+((\y->y+1) 2)  --There is comment
              where  
                  addThree a b c = (a + b) + c  

main =foo 10