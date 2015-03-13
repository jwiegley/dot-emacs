module Infix2 where
data T1 a b = b :#: a
 
f x y
    =   (error
             "x :$: y no longer defined for T1 at line: 5")
 