module PolyRec where

data A a = A a (A a) | B (A Int)


poly :: Show a => A a -> String
poly (A x a) = "A "++show x++poly a
poly (B a) = "B "++poly a

mono (A x a) = "A "++show x++mono a
mono (B a) = "B "++mono a
