module Test1 where

-- folding against a simple function definition, the instance of g should be replaced with a function call
-- to f x (or f 1)

f x = x + 1

g = f 1
