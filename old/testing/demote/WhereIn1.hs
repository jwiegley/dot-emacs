module WhereIn1 where

--A definition can be demoted to the local 'where' binding of a friend declaration,
--if it is only used by this friend declaration.

--Demoting a definition narrows down the scope of the definition.
--In this example, demote the top level 'sq' to 'sumSquares'
--This example also aims to test the adding of a 'where' claus.

sumSquares x y = sq x + sq y       

sq 0 = 0
sq z = z^pow

pow=2

anotherFun 0 y = sq y
     where  sq x = x^2

