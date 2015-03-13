{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances, UndecidableInstances, FunctionalDependencies, NoMonomorphismRestriction #-}
{-+
Functions for unifying types, matching types, and expanding type synonyms.
-}
module TiSolve(TypeConstraint(..),solve,isVar,matches,matchEqns,expandSynonyms) where
import Prelude hiding (lookup) -- for Hugs
import Control.Monad(mplus)
import TiConstraints
import TiTypes
import TiNames
import TiKinds
import TiPrelude(funcon)
import Unification(Unifiable(..),unify,match)
import MUtils
import Syntax(HsTypeI(..),TI(..),HsIdentI(..),matchT,struct,mapT,base)
import TiKEnv(lookup)
import PrettyPrint(Printable,pp)

--------------------------------------------------------------------------------
data TypeConstraint i
  = Type i :=: Type i
  | Inst (Typing i (Pred i))
  | KInst (Kinded (Type i)) -- to keep track of the kinds of type variables
  deriving Show

instance TypeVar v => Types v (TypeConstraint v) where
  tmap f (t1:=:t2) = tmap f t1:=:tmap f t2
  tmap f (Inst i) = Inst (tmap f i)
  tmap f (KInst (t:>:k)) = KInst (tmap f t:>:k)
  tv (t1:=:t2) = tv (t1,t2)
  tv (Inst i) = tv i
  tv (KInst (t:>:k)) = tv t

--------------------------------------------------------------------------------

solve env constraints =
    do let (eqns,(preds0,kpreds0)) = separate (toList constraints)
       s <- S # unify (expandEqns env eqns)
       let preds = apply s preds0
           kpreds = [apply s t:>:k|t:>:k<-kpreds0]
       return (preds,kpreds,s)
  where
    separate = apSnd (mapPartition id) . mapPartition dist
    dist (t1:=:t2) = Left (t1,t2)
    dist (Inst i) = Right (Left i)
    dist (KInst ki) = Right (Right ki)

t1 `matches` t2 = matchEqns [(t2,t1)]
matchEqns eqns env =  S # match (expandEqns env eqns)

instance (Printable i,TypeId i) => Unifiable (Type i) i where
  topMatch (Typ t1,Typ t2) =
    matchT t1 t2 `mplus` matchT (tupleHack t1) (tupleHack t2)

  isVar = isVarT
  subst s t = apply (S s) t

  showTerm = pp

{-+
Function types (previously also tuple types) can be represented in two
different ways in the abstract syntax, so we convert one
representation to the other to avoid false unification/matching
errors...
-}
--tupleHack (HsTyTuple ts) = struct $ appT (tuplecon (length ts):ts)
tupleHack (HsTyFun t1 t2) = struct $ appT [funcon,t1,t2]
tupleHack t = t

expandEqns env = mapBoth (expandSynonyms env)

{-+
Expand type synonyms.
(Previously, this function also replaced data/newtype names with their
original names. This is now assumed to happen in a pass prior to type checking.)
-}

--expandSynonyms :: Env QId (Kind,TypeInfo) -> Type -> Type
expandSynonyms env (Typ t) =
  case t of
    HsTyApp t1 t2 -> expandApp t1 [t2]
    HsTyCon _     -> expandApp (base t) []
    _ -> base $ mapT (expandSynonyms env) t
 where
   --expandApp :: Type -> [Type] -> Type
   expandApp (Typ t) ts = 
     case t of
       HsTyApp t1 t2 -> expandApp t1 (t2:ts)
       HsTyCon c ->
         case TiKEnv.lookup env (HsCon c) of
	   --Just (_,Data orig) -> app (HsTyCon orig)
	   --Just (_,Newtype orig) -> app (HsTyCon orig)
           Just (_,Synonym vs rhs) | n<=length ts ->
	       expandSynonyms env (appT (apply (S (zip vs ts1)) rhs:ts2))
	     where
               n=length vs
	       (ts1,ts2) = splitAt n ts
	   _ -> keepApp
       _ -> keepApp
     where
       keepApp = app t
       app t =  appT (base t:map (expandSynonyms env) ts)
