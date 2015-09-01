module Infix3 where

-- define an infix constructor and attempt to remove it...

data T1 a b = a :$: b | b :#: a


g :: T1 Int Int -> Int
g (x :$: y) = x + y
g (x :#: y) = y - x

f x y = g (x :$: y)