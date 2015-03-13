module Errors (totallyUnknownEntity)  where
import Errors (Foo)
import Prelude (foobar)
import Bubba   (foobar)

infixr 3 %%


data P x = Foo (x,x)
data Q x = Bar (x,x)


class BarBar x where
  a :: x -> x

data C = P Q

data P x = PP x

data BarBar x = BB x

instance BarBar P where
  a x = x

c = B.f

data YY x x = PPPP x -- repeaated type variable on lhs
type Q x = Q x -- recursive type synonym


data P x = Q (x -> x) 
  deriving Show
{- ^ Cannot derive instances for types with polymorphic or qualified components
 -}

data P x = Q (x -> z -> x)
    deriving Show

newtype P x = A (x,x) -- Variable "x" in constraint is not locally bound
newtype P a b = X a b -- A newtype constructor must have exactly one argument
newtype P a b = X !a --  Illegal strictess annotation for newtype constructor
data Foo x = Bar x
           | Foo x
           | Bar x --  Repeated definition for constructor function "Bar"
data P x = Foo { a :: x, b :: String, a :: String } --Repeated field name "a" for constructor "Foo" 