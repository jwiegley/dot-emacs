module FunIn1 where

--Default parameters can be added to definition of functions and simple constants.

--In this example: add parameter 'y' to 'foo'
foo :: a -> Int -> Int
foo y  x= h + t where (h,t) = head $ zip [1..x] [3..15] {-There 
is a comment-}

foo_y = undefined

main :: Int
main = (foo foo_y) 4 