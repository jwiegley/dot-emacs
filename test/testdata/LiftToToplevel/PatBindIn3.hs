module LiftToToplevel.PatBindIn3 where

--A definition can be lifted from a where or let to the top level binding group.
--Lifting a definition widens the scope of the definition.

--In this example, lift 'sq' defined in 'sumSquares'
--This example aims to test changing a constant to a function.

sumSquares x = sq + sq
           where
              sq = x^pow
              pow =2
                 
anotherFun 0 y = sq y
     where sq x = x^2

