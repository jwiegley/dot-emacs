module Partial1 where

data P a b = C1 a b | C2 a b b


f x y = (C1 x) y 