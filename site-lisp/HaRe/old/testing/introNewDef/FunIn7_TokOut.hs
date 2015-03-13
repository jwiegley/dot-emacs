module FunIn7 where

--A new definition can be introduced to denote an identified sub-expression.
--The newly introduced definition may be a function binding
--or a simple constant binding. The new binding will be put at the end of the 
--local 'where' or 'let' clause depending on the scope of high lighted source.

--This example aims to test that the name definition name should be fresh.

foo x=z*w +z*w*5 where  z=3
                        w=5  {-there is 
a comment-}

main=foo 10

