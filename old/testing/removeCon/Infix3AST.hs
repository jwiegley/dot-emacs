module Infix3 where
data T1 a b = b :#: a
 
g :: (T1 Int Int) -> Int
 
g ((x :#: y)) = y - x
 
f x y
    =   g   (error
                 "x :$: y no longer defined for T1 at line: 5")
 