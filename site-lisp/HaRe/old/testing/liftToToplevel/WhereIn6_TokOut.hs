module WhereIn6 where

--A definition can be lifted from a where or let to the top level binding group.
--Lifting a definition widens the scope of the definition.

--In this example, lift 'pow' defined in  'sq'

sumSquares x y = sq x + sq y        
           where 
                 sq::Int->Int
                 sq 0 = 0
                 sq z = z^pow

pow=2                

                      
anotherFun 0 y = sq y
     where sq x=x^2

