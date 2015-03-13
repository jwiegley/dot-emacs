module Case2 where

data T a = C1 a | C2 Float  


addedC2 = error "added C2 Float to T"
-- f (C1 x) = x
f :: T a -> Int
f x =   case g of
            (C1 x) -> x
  where g = C1 42
