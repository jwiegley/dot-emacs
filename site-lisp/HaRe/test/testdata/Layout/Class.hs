module Layout.Class where

class Foo a where
  foo :: a -> Int -> Char

instance Foo Double where
  foo p1 p2 = 'a'


