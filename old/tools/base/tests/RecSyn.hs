module RecSyn where

--type K = L
--type L a = Maybe (a,L a)

nil = Nothing
cons x xs = Just (x,xs)

single x = cons x nil

type Rec a = [Circ a]
--data Circ a = Tag [Rec a]
type Circ a = [Rec a]


class A a => B a where
  b :: a->a

class B a => A a where
  a :: a->a
