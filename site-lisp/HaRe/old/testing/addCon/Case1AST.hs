module Case1 where
data T a = C1 a | C3 Int | C2 Float
 
addedC3 = error "added C3 Int to T"
 
addedC2 = error "added C2 Float to T"
 
f x =   case g of
            (C1 x) -> x
            (C3 a) -> addedC3
  where g = C1 x
 