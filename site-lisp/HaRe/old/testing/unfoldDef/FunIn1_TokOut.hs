module FunIn1 where

--The application of a function is replaced by the right-hand side of the definition,
--with actual parameters replacing formals.

--In this example, unfold 'addthree'.
--This example aims to test unfolding a constant.

main :: Int -> Int
main = \x -> case x of
                1 -> 1 + main 0
                0 -> (app (\ a b c -> (a + b) + c) 1 2 3) 

app :: (a -> b) -> a -> b
app = \f x -> f x

addthree :: Int -> Int -> Int -> Int
addthree = \a b c -> a + b + c
