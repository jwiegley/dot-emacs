module Demote.LetIn2 where

--A definition can be demoted to the local 'where' binding of a friend declaration,
--if it is only used by this friend declaration.

--Demoting a definition narrows down the scope of the definition.
--In this example, demote the local  'pow' will fail.

sumSquares x y = let sq 0=0
                     sq z=z^pow
                     pow=2
                 in sq x + sq y +pow 
                      
         
anotherFun 0 y = sq y
     where  sq x = x^2

  