module PatIn2 where

--Default parameters can be added to definition of functions and simple constants.

--In this example: add parameter 'x' to '(h,t)' will fail.
foo :: Int
foo = h + t where (h,t) = head $ zip [1..10] [3..15]

main :: Int
main = foo 