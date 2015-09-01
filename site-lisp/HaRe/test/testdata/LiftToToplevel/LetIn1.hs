module LiftToToplevel.LetIn1 where

--A definition can be lifted from a where or let to the top level binding group.
--Lifting a definition widens the scope of the definition.

--In this example, lift 'sq' in 'sumSquares'
--This example aims to test lifting a definition from a let clause to top level,
--and the elimination of the keywords 'let' and 'in'

sumSquares x y = let sq 0=0
                     sq z=z^pow
                  in sq x + sq y
                       where pow=2

anotherFun 0 y = sq y
     where sq x = x^2
