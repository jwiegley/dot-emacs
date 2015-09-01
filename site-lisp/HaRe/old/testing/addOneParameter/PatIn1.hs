module PatIn1 where

--Default parameters can be added to definition of functions and simple constants.

--In this example: add parameter 'x' to 'foo'
foo :: Int
foo = h + t where (h,t) = head $ zip [1..10] [3..15]

main :: Int
main = foo 