module Deriving where

data A = A1 A | A2 B deriving (Eq)

data B = B1 Int | B2 A deriving (Eq)


--s = show (B2 (A2 (B1 5)))


data T1 a b c = C1 a (T2 a b c) deriving (Eq,Show)
data T2 a b c = C2 (T3 a b c) | C2b (N b) deriving (Eq,Show)
data T3 a b c = C3 (N c) (T1 a c b) deriving (Eq,Show)


data N b = N b deriving Show
instance Eq (N b) where _==_=True
