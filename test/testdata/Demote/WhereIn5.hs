module Demote.WhereIn5 where

--A definition can be demoted to the local 'where' binding of a friend declaration,
--if it is only used by this friend declaration.

--Demoting a definition narrows down the scope of the definition.
--In this example, demote the top level 'pow' to 'sq'
--This example aims to test demoting a function/pattern binding multi-levels.

sumSquares x y = sq x + sq y
         where sq 0=0
               sq z=z^pow {-There 
is a comment-}
pow=2

anotherFun 0 y = sq y
     where  sq x = x^2

