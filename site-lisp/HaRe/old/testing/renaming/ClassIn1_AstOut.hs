module ClassIn1 where
class MyReversable a
  where
      myreverse :: a -> a
      myreverse _ = undefined
 
instance MyReversable [a] where myreverse = reverse
 
data Foo = Boo | Moo
 
instance Eq Foo
  where
      (==) Boo Boo = True
      (==) Moo Moo = True
      (==) _ _ = False
 
main = myreverse [1, 2, 3]
 