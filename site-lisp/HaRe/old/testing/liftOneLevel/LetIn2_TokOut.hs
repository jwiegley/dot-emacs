module LetIn2 where

--A definition can be lifted from a where or let into the surronding binding group.
--Lifting a definition widens the scope of the definition.

--In this example, lift 'sq' in 'sumSquares'
--This example aims to test lifting a definition from a let clause to a where clause,
--adding parameters and the keyword 'where'.

sumSquares x y = let 
                     pow=2
                  in (sq pow) x + (sq pow) y        
  where
    sq pow 0=0
    sq pow z=z^pow
                     

anotherFun 0 y = sq y
     where  sq x = x^2
