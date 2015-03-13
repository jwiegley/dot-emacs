module FunDep where
import Maybe

class C a b | a->b where f :: a->b

instance C [a] a where f = head

instance C a b => C (Maybe a) (Maybe b) where f = fmap f
--instance (Functor f,C a b) => C (f a) (f b) where f = fmap f

instance C Bool Int where f = fromEnum
instance C Int String where f = show


f2 x = f (f x)

z = f False
s = f2 False
