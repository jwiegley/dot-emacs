module ClassIn2 where
class Reversable a
  where
      reversable :: a -> a
      reversable _ = undefined
 
instance Reversable [a] where reversable = reverse
 
data Foo = Boo | Moo
 
instance Eq Foo
  where
      (==) Boo Boo = True
      (==) Moo Moo = True
      (==) _ _ = False
 
main = reversable [1, 2, 3]
 