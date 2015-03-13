module Infix4 (f) where

-- define an infix constructor and attempt to remove it...

data T1 a b = a :$: b | b :#: a


g :: T1 Int Int -> Int
g (x :$: y) = x + y


f x y = g (x :$: y)