module Primes where

primes = sieve [2..]

sieve [] = []
sieve (x:xs) = x:sieve [y|y<-xs, y `mod` x /= 0]

{-P:
assert PrimesProp = {-#cert:QcPrimesProp#-} {-#cert:ISayPrimesProp#-}
  All i . {i>=0}:::True ==> {primes!!i} ::: TwoOrOdd

property TwoOrOdd x = x===2 \/ True{odd x}

--two = 2

isTwoOrOdd x = x==2 || odd x

property SieveProp = {| n::Integer | {all isTwoOrOdd (sieve [2..n])} ::: True |}

assert PrimesProp100 = SieveProp 10 {-#cert:QcPrimesProp100#-} {-#cert:AlfaPrimesProp100#-}
assert PrimesPropAll = All n . SieveProp n

-}
