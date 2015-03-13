{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances, UndecidableInstances, FunctionalDependencies, NoMonomorphismRestriction #-}
{-+
This module defines the represenation of types, qualified types, type schemes,
substitution and various auxiliary types.
-}
module TiTypes(module TiTypes,HsTypeI(..),HsIdentI(..),Kind) where
import Syntax(HsTypeI(..),TI(..),HsIdentI(..),HsFunDeps,
              hsTyFun,hsTyApp,hsTyTuple,hsTyCon,hsTyVar,
              kstar,base,mapTI,accT)
import Data.List(nub,(\\))
import Data.Maybe(fromMaybe)
import MUtils(collectByFst)
--import TiEnv(Env,range)
import TiKinds(Kind)
import TiNames
import Debug.Trace(trace) -- for debugging

type Type i = HsTypeI i
type Pred i = Type i
data Qual i t = [Pred i] :=> t deriving (Eq,Show,Read)
type QType i = Qual i (Type i)

data Scheme v = Forall [Kinded v] [Kinded v] (QType v)
              deriving (Eq,Show,Read) -- Eq??

unQual t = []:=>t
forall' = Forall []
mono t = forall' [] (unQual t)
--uscheme qt = fakeForall (tv qt) qt --  temporary hack!!!
--  where fakeForall vs qt = Forall (map (:>:kstar) vs) qt --  temporary hack!!!
--upscheme t = uscheme (unQual t) --  temporary hack!!!
kuscheme ks qt = forall' (kinded ks (tv qt)) qt
kupscheme ks t = kuscheme ks (unQual t)

funT ts = foldr1 hsTyFun ts -- :: Type
appT ts = foldl1 hsTyApp ts -- :: Type
tupleT ts = hsTyTuple ts -- :: Type
tyvar v = hsTyVar v -- :: Tyvar -> Type
ty (HsVar v) = tyvar v
ty (HsCon c) = hsTyCon c -- :: Type

isVarT (Typ (HsTyVar v)) = Just v
isVarT _ = Nothing

isFunT (Typ (HsTyFun t1 t2)) = Just (t1,t2)
isFunT _ = Nothing

flatAppT t = flat t []
  where
    flat (Typ (HsTyApp t1 t2)) ts = flat t1 (t2:ts)
    flat t ts = (t,ts)


flatConAppT ty =
  case flatAppT ty of
    (Typ (HsTyCon c),ts) -> Just (HsCon c,ts)
    _ -> Nothing

--instName (SrcLoc f l c) = HsVar (Qual (Module "i") (show l++"_"++show c))
--dictName n = HsVar (Qual (Module "d") n) :: QId
--vvar = unqual :: String->VarId

infix 1 :>:
data Typing x t = x :>: t deriving (Eq,Show,Read)
type Assump i = Typing (HsIdentI i) (Scheme i)
type Typed i x = Typing x (Type i)

emap f (e :>: t) = f e:>:t
tdom xts = [x|x:>:_<-xts]

unzipTyped :: [Typing x t] -> Typing [x] [t]
unzipTyped ets = uncurry (:>:) $ unzip [(e,t)|e:>:t<-ets]

zipTyped :: Typing [x] [t] -> [Typing x t]
zipTyped (xs:>:ts) = zipWith (:>:) xs ts

--collectTyped :: Ord x => [Typing x t] -> [Typing x [t]]
collectTyped xts = map (uncurry (:>:)) $ collectByFst [(x,t)|x:>:t<-xts]


type Kinded x = Typing x Kind
kinded1 ks v = v:>:head' [k|HsVar v':>:k<-ks,v'==v] -- not very efficient...
  where head' [] = trace ("Bug in TiTypes.kinded1: missing kind info for "++show v) kstar
	head' (k:_) = k
kinded ks = map (kinded1 ks)
--type KAssump = Typing Id Kind

type KInfo i = [Typing (HsIdentI i) (TypeInfo i)]

data TypeInfo i
  = Data
  | Newtype
  | Class [Pred i]        -- superclasses
          [Kinded i]      -- parameters
          (HsFunDeps Int) -- fun deps (0-based parameter positions)
          [Assump i]      -- methods
  | Synonym [i] (Type i)
  | Tyvar
  deriving ({-Eq,-}Show,Read)

newtype Subst i = S [(i,Type i)] deriving (Show)

idS = S []
infix 5 +->
v+-> t = S [(v,t)]
extS v t s = compS (v+->t) s
compS s1@(S s1') s2 = S (s1'++s2')
   where S s2' = apply s1 s2
domS (S s) = map fst s

varSubst s@(S s') v = fromMaybe (tyvar v) (lookup v s')

applySubst s@(S s') ty@(Typ t) =
    case t of
      HsTyVar v -> fromMaybe ty (lookup v s')
      _ -> base $ mapTI id (applySubst s) t

class TypeVar v => Types v t | t->v where
  tmap :: (Type v->Type v) -> t -> t
  apply :: Subst v -> t -> t
  tv :: t -> Set v

  apply = tmap . applySubst

type Set a = [a]

occurs v t = v `elem` tv t

instance Types v t => Types v [t] where
  tmap = map . tmap
  tv = nub . concatMap tv

instance TypeVar v => Types v (Subst v) where
  tmap f (S s') = S [(v,tmap f t)|(v,t)<-s'] -- hmm
  tv (S s') = tv (map snd s') -- hmm

instance (Types v t1,Types v t2) => Types v (t1,t2) where
  tmap f (t1,t2) = (tmap f t1,tmap f t2)
  tv (t1,t2) = nub (tv t1++tv t2)

instance (Types v t1,Types v t2,Types v t3) => Types v (t1,t2,t3) where
  tmap f (t1,t2,t3) = (tmap f t1,tmap f t2,tmap f t3)
  tv (t1,t2,t3) = nub (tv t1++tv t2++tv t3)

instance Types v t => Types v (Typing x t) where
  tmap f (x:>:t) = x:>:tmap f t
  tv (x:>:t) = tv t

instance Functor (Typing x) where
  fmap f (x:>:t) = x:>:f t -- hmm

instance TypeVar v => Types v (Type v) where
  tmap = id
  tv (Typ t) =
    case t of
      HsTyVar v -> [v]
      HsTyForall vs ps t -> tv (ps,t) \\ vs
      _ -> nub $ accT ((++) . tv) t []

instance TypeVar v => Types v (Scheme v) where
  apply s (Forall ags gs qt) = Forall ags gs (apply (restrict s (tdom (ags++gs))) qt)
  tmap f (Forall ags gs qt) = Forall ags gs (tmap f qt) -- hmm
  tv (Forall ags gs qt) = tv qt \\ tdom (ags++gs)

restrict (S s) gs = S [s1|s1@(v,_)<-s,v `notElem` gs]

instance Types v t => Types v (Qual v t) where
  tmap f (ps:=>t) = tmap f ps:=>tmap f t
  tv (ps:=>t) = tv (ps,t)
{-
instance Types v info => Types v (Env key info) where
  tmap = fmap . tmap
  tv = tv . range
-}
