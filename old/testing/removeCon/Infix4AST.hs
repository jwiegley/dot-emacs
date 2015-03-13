module Infix4 (f) where
data T1 a b = b :#: a
 
f x y
    =   error
            "g (x :$: y) no longer defined for T1 at line: 5"
 