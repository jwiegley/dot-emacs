module LiftOneLevel.LetIn1 where

--A definition can be lifted from a where or let into the surronding binding group.
--Lifting a definition widens the scope of the definition.

--In this example, lift 'sq' in 'sumSquares'
--This example aims to test lifting a definition from a let clause to a where clause,
--and the elimination of the keywords 'let' and 'in'

sumSquares x y = let sq 0=0
                     sq z=z^pow
                  in sq x + sq y
                       where pow=2

anotherFun 0 y = sq y
     where sq x = x^2
