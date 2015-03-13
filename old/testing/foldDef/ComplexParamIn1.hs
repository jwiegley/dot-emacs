module ComplexParamIn1 where

--The application of a function is replaced by the right-hand side of the definition,
--with actual parameters replacing formals.

--In this example, unfold the first 'sq' in 'sumSquares'
--This example aims to test unfolding a definition with guards.

sumSquares x y = (case (x, y) of
                      (m, n) -> m ^ n)
 
sq (m,n)=m^n
