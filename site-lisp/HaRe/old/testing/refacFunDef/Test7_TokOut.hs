module Test7 where

-- uses a variable in the lhs of f which is not used

f x y = y + 1

g = f undefined 1


