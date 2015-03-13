{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances, UndecidableInstances, FunctionalDependencies, NoMonomorphismRestriction #-}
module TiFresh where
import TiMonad(IM,freshInt)
import TiTypes
import MUtils
import TiKinds

class Fresh a where
  fresh :: IM i c a

freshlist n = sequence (replicate n fresh)

instance Fresh Int where
  fresh = freshInt

instance Fresh String where
  fresh = (show::Int->String) # fresh

--instance Fresh Tyvar where
--  fresh = tvar # fresh

instance (Fresh a,Fresh b) => Fresh (a,b) where
  fresh = (,) # fresh <# fresh

instance Fresh i => Fresh (Type i) where
  fresh = tyvar # fresh

instance Fresh i => Fresh (Scheme i) where
  fresh = forall' [] # fresh

instance Fresh t => Fresh (Qual i t) where
  fresh = ([]:=>) # fresh

--instance Fresh QId where
--  fresh = dictName # fresh

instance Fresh KVar where
  fresh = KVar # fresh

instance Fresh Kind where
  fresh = Kvar # fresh

instance Fresh (TypeInfo i) where
  fresh = return Tyvar

