module GuardIn1 where

--The application of a function is replaced by the right-hand side of the definition,
--with actual parameters replacing formals.

--In this example, unfold the first 'sq' in 'sumSquares'
--This example aims to test unfolding a definition with guards.

sumSquares x y = (if x == 0 then 0 else x ^ pow) + sq y 
 
sq x
  |x==0     = 0
  |otherwise= x^pow

pow=2