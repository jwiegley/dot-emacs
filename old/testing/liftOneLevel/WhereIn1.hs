module WhereIn1 where

--A definition can be lifted from a where or let into the surronding binding group.
--Lifting a definition widens the scope of the definition.

--In this example, lift 'sq' in 'sumSquares'
--This example aims to test add parameters to 'sq'.

sumSquares x y = sq x + sq y        
           where 
                 sq 0 = 0
                 sq z = z^pow
                 pow=2

anotherFun 0 y = sq y
     where  sq x = x^2
