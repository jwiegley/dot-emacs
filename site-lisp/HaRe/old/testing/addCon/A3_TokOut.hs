module A3 where

data T n a = C1 a  | C2 Int n  


addedC2 = error "added C2 Int n to T"

over :: (T n b) -> b
over (C1 x) = x
over (C2 a b) = addedC2

