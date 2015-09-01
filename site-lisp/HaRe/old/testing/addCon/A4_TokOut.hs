module A4 where

data T b a = C1 a  | C2 b  


addedC2 = error "added C2 b to T"

over :: (T b_1 b) -> b
over (C1 x) = x
over (C2 a) = addedC2

under :: (T b a) -> a
under (C1 x) = x
under (C2 a) = addedC2
