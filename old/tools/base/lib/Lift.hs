{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances, UndecidableInstances, FunctionalDependencies, NoMonomorphismRestriction #-}
module Lift where
import Data.Maybe(maybeToList)
import PrettyPrint

---
-- An experiment:

class Lift m1 m2 where
  lift :: m1 a -> m2 a

instance (Printable err,Monad m) => Lift (Either err) m where
  lift = either (fail.pp) return

instance Lift Maybe [] where
  lift = maybeToList
