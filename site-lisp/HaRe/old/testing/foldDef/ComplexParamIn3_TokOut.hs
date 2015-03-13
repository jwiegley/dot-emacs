module ComplexParamIn3 where

--The application of a function is replaced by the right-hand side of the definition,
--with actual parameters replacing formals.


data Tup a b = Tup a b


--In this example, unfold the first 'sq' in 'sumSquares'
--This example aims to test unfolding a definition with guards.

sumSquares x y = (case (x, y) of
                      (m, n) -> sq (Tup undefined m))
 
sq (Tup n m) = m^2
