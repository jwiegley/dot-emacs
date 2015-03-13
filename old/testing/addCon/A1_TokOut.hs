module A1 where

data T c a = C1 a | C2 c  


addedC2 = error "added C2 c to T"

over :: (T c b) -> b
over (C1 x) = x
over (C2 a) = addedC2

