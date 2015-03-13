module Test6 where

-- uses a variable in the lhs of f which is not used

f x y = x + 1

g = f 1 undefined


