module LiftToToplevel.WhereIn2 where

--A definition can be lifted from a where or let to the top level binding group.
--Lifting a definition widens the scope of the definition.

--In this example, lift 'sq' in 'sumSquares'
--This example aims to test renaming.

sumSquares x y = sq x + sq y
           where
                 sq 0 = 0
                 sq z = z^pow --This is a comment
                 pow=2

anotherFun 0 y = sq y
     where sq x = x^2

sq x =x ^2
