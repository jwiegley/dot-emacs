module FunIn3 where

--The application of a function is replaced by the right-hand side of the definition,
--with actual parameters replacing formals.

--In this example, unfold 'addthree'.
--This example aims to test the elimination of extra parentheses when unfolding
--a function defintion.

main :: Int -> Int
main = \x -> case x of
                1 -> 1 + main 0
                0 ->((1 + 2) + 3)


addthree :: Int -> Int -> Int -> Int
addthree a b c = a + b + c
