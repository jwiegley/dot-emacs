module FunIn7 where

--A complex pattern binding can not be generalised.In this example, generalise the literals in
--'tup@(h,t)' will fail.


main :: Int
main = foo + 17

foo = h + t + (snd tup)

tup@(h,t) = head $ zip [1..10] [3..15]


