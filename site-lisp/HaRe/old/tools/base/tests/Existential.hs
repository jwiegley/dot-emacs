module Existential where

-- Hmm, this is universal quantification, not existential.
data U = U (forall a . (a,a->Int,Int->a,a->a->a))

-- This is existential quantification
data E = forall a . {-Eq a =>-} E (a,a->Int,Int->a,a->a->a)

e = E (1,id,id,(+))

-- OK:
f (E (x,toint,fromint,op)) = toint (x `op` x)

-- Error: it assumes that the existentially quantified type is Bool
--g (E (x,toint,fromint,op)) = toint (False `op` x)

-- Error: assuming two different existentially quantifier variables are the same
--h (E (_,toint,_,_)) (E (x,_,_,_)) = toint x

-- Error: the existentially quantified type variable escapes
-- (and becomes universally quantified)
--j (E (x,_,_,_)) = x
