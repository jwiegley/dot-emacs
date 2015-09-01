module FunDep4 where


class A e a | a->e where a :: a->a; e :: a->e
class B a where b :: a->a

class (A e a,B a) => C e a
instance (A e a,B a) => C e a

f :: C e a => a->a
f x = a (b x)
