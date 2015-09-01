{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances, UndecidableInstances, FunctionalDependencies, NoMonomorphismRestriction #-}
{-+
Types for kinds.
Functions for kind inference. 
-}
module TiKinds(module TiKinds,kstar,kpred) where
import HsKind(K(..),mapK,matchK)
--import HsDeclStruct(HsFunDeps)
import HasBaseStruct(HasBaseStruct(..),kstar,kpred)
import TiConstraints
import Unification(Unifiable(..),unify)
import PrettyPrint

-- Be strict to avoid a space leak
data Kind = K !(K Kind) | Kvar KVar deriving (Eq,Show,Read)
newtype KVar = KVar Int deriving (Eq,Show,Read)

instance HasBaseStruct Kind (K Kind) where base = K

data KindConstraint = Kind :=* Kind deriving (Show)
type KSubst = [(KVar,Kind)]

fixkvars :: Kind -> Kind
fixkvars k =
  case k of
    Kvar _ -> kstar
    K k -> K $ mapK fixkvars k

ksubst :: KSubst -> Kind -> Kind
ksubst s k =
  case k of
    K k -> K $ mapK (ksubst s) k
    Kvar kv -> case lookup kv s of
	         Just k' -> k'
		 _ -> k

ksolve :: Monad m => Constraints KindConstraint -> m KSubst
ksolve cs = unify [(k1,k2)|k1:=*k2<-toList cs]

ksolveSloppy cs = unify [(sloppy k1,sloppy k2)|k1:=*k2<-toList cs]
  where
    sloppy k =
      case k of
	Kvar _ -> k
	K Kpred -> K Kstar
	K k -> K $ mapK sloppy k

instance Unifiable Kind KVar where
  topMatch (Kvar kv1,Kvar kv2) | kv1==kv2 = Just []
  topMatch (K k1,K k2) = matchK k1 k2
  topMatch _ = Nothing

  isVar (Kvar kv) = Just kv
  isVar _ = Nothing

  subst = ksubst

  showTerm = pp

---

--instance Show Kind where show = pp
instance Printable Kind where
  ppi (K k) = ppi k
  ppi (Kvar kv) = ppi kv

  wrap (K k) = wrap k
  wrap k = ppi k

instance Printable KVar where
  ppi (KVar k) = ppi ("k"++show k)
  wrap = ppi
