module LiftToToplevel.WhereIn7 where

--A definition can be lifted from a where or let to the top level binding group.
--Lifting a definition widens the scope of the definition.

--In this example, lift 'addthree' defined in 'fun'.
--This example aims to test adding parenthese.


fun x y z =inc addthree
       where inc a =a +1
             addthree=x+y+z
