module WhereIn5 where

--A definition can be lifted from a where or let into the surronding binding group.
--Lifting a definition widens the scope of the definition.

--In this example, lift 'sq' in 'sumSquares'
--This example aims to test the lifting of type signature.

sumSquares x y = (sq_1 pow) x + rt y        
           where 
                 rt :: Int -> Int
                 rt x = x^pow^pow 
                 pow=2

sq_1 pow 0 = 0
sq_1 pow z = z^pow
                 

anotherFun 0 y = sq y

sq x = x^2
