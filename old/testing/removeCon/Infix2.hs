module Infix2 where

-- define an infix constructor and attempt to remove it...

data T1 a b = a :$: b | b :#: a


f x y = x :$: y