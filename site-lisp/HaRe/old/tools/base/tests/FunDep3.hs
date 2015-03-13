module FunDep3 where

data Zero = Zero deriving (Show)
newtype Succ n = Succ n deriving (Show)

one = Succ Zero
two = Succ one

class Add a b c | a b -> c where add :: a -> b -> c

instance Add Zero b b where add _ b = b
instance Add a b c => Add (Succ a) b (Succ c) where
    add (Succ a) b = Succ (add a b)

double n = add n n

three = add one two
four = double two
eight = double four

class Mul a b c | a b -> c where mul :: a -> b -> c

instance Mul Zero b Zero where mul _ _ = Zero
instance (Mul a b c1,Add b c1 c) => Mul (Succ a) b c where
  mul (Succ a) b = add b (mul a b)

nine = mul three three

n36 = mul four nine
