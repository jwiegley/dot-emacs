{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
module Substitute where
import Recursive

{-+
The intention with class #Subst# is that #subst s e# applies the
subsitution #s# to all variables occuring in #e#.

It is assumed that name capture will not happen, i.e., #s# does not
affect variables that are bound in (parts of) #e#, and if #x# is free
in e, #s x# does not contain variables that become bound when
substituted into #e#.
-}

class Subst i e | e->i where
  subst :: (i->e) -> e->e

{-+
The intention with class #MapExp# is that #mapExp f e# applies the
function #f# to every expression occuring in a larger structure (e.g.,
a list of declarations). Instances of #Subst# will typically make use of
instances of #MapExp#.
-}

class MapExp e s | s->e where
  mapExp :: (e->e) -> s->s

instance MapExp e s => MapExp e [s] where mapExp = map . mapExp

esubst = mapExp . subst

esubst1 var e x = esubst s
  where
    s y = if y==x then e else var y

mapExpRec = mapRec . mapExp

{-
class Subst i e s1 s2 | e->i,s1->i, where
  subst :: (i->e)->s1->s2
-}
