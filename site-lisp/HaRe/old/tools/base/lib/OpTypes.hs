module OpTypes where

type EqOp a     = a -> a -> Bool
type OrdOp a    = a -> a -> Bool
type CmpOp a    = a -> a -> Ordering


eqBy :: Eq a => (b -> a) -> EqOp b
eqBy f x y      = f x == f y

ordBy :: Ord a => (b -> a) -> OrdOp b
ordBy f x y      = f x <= f y

cmpBy :: Ord a => (b -> a) -> CmpOp b
cmpBy f x y      = f x `compare` f y
