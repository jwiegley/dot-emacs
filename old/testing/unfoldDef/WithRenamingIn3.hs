module WithRenamingIn3 where

--The application of a function is replaced by the right-hand side of the definition,
--with actual parameters replacing formals.

--In this example, unfold  'sq' in 'sumSquares'
--This example aims to test renaming in order to avoid name clash or capture.

partialSquare pow =sq pow
 
sq x pow=x^pow
