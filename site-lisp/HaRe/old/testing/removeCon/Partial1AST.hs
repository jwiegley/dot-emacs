module Partial1 where
data P a b = C2 a b b
 
f x y
    =   ((error "C1 no longer defined for P at line: 3")
             x)
            y
 