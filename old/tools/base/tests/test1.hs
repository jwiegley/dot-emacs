

infixr 6 :<
infixl 5 ++
infixl 9 **

data  Int = Z | S Int

data MyList a = Nil
              | a :< (MyList a)

Nil ++ x = x
(a :< as) ++ x = a :< (as ++ x)

Nil ** x = Nil
(a :< as) ** x = a :< (x ** as)



class VC a where
   rpl :: a -> (MyList a)

instance VC a => VC (MyList a) where
  rpl x = (rpl x) :< rpl x

instance VC Int where
  rpl x = x :< (rpl x)

p12 = S (S Z)
q12 = rpl p12