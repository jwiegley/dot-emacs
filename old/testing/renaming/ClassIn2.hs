module ClassIn2  where

--Any class/instance name declared in this module can be renamed

--Rename instance name 'myreverse' to 'reversable'

class Reversable a where
  myreverse :: a -> a
  myreverse _ = undefined

instance Reversable [a] where
  myreverse = reverse

data Foo = Boo | Moo 
 
instance Eq Foo where
   Boo == Boo = True
   Moo == Moo = True
   _   == _   = False

main = myreverse [1,2,3]

