module WithLocalDeclIn2 where

--The application of a function is replaced by the right-hand side of the definition,
--with actual parameters replacing formals.

--In this example, unfold  the first 'sq' in 'sumSquares'
--This example aims to test unfolding a  function with local declarations.

sumSquares x y =(let pow = 2 in x ^ pow) + sq y
 
sq x=x^pow
     where pow=2
