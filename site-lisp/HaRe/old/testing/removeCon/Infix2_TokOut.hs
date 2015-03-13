module Infix2 where

-- define an infix constructor and attempt to remove it...

data T1 a b = b :#: a


f x y = (error "x :$: y no longer defined for T1 at line: 5")