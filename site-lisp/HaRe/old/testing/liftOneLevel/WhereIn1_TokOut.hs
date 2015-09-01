module WhereIn1 where

--A definition can be lifted from a where or let into the surronding binding group.
--Lifting a definition widens the scope of the definition.

--In this example, lift 'sq' in 'sumSquares'
--This example aims to test add parameters to 'sq'.

sumSquares x y = (sq pow) x + (sq pow) y        
           where 
                 pow=2

sq pow 0 = 0
sq pow z = z^pow


anotherFun 0 y = sq y
     where  sq x = x^2
