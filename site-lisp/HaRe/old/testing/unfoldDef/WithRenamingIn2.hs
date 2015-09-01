module WithRenamingIn2 where

--The application of a function is replaced by the right-hand side of the definition,
--with actual parameters replacing formals.

--In this example, unfold  the first 'sq' in 'sumSquares'
--This example aims to test renaming in order to avoid name clash or capture.

sumSquares pow y =sq pow + sq y 
 
sq x=x^pow
   where pow=2
