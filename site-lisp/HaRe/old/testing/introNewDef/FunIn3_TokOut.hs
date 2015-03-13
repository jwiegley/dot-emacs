module FunIn3 where

--A new definition can be introduced to denote an identified sub-expression.
--The newly introduced definition may be a function binding
--or a simple constant binding. The new binding will be put at the end of the 
--local 'where' or 'let' clause depending on the scope of high lighted source.

--In this example: Introduce a new definition to denote 'x*5*z'

foo x=xz*w where  z=3
                  w=5  {-there is a comment-}
                  xz = (x * 5) * z
                     

main=foo 10

