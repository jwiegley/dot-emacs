module Demote.WhereIn6 where

--A definition can be demoted to the local 'where' binding of a friend declaration,
--if it is only used by this friend declaration.

--Demoting a definition narrows down the scope of the definition.
--In this example, demote the top level 'addthree' to 'fun'
--This example also aims to test the removing of parameters and parentheses.

fun x y z =inc (addthree x y z)
       where inc a =a +1

addthree a b c=a+b+c


