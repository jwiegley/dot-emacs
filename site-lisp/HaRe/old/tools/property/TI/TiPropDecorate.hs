{-+
This module provides type inference for the base+property syntax.
This type checker outputs an abstract syntax tree where all declaration lists
have been decorated with the kinds and types of the entities defined in
the list, and all applications of polymorphic functions have been decorated
with the instantiation of the quantified variables.
-}
module TiPropDecorate where
import PropSyntaxStruct
import HasBaseStruct
import HasPropStruct
import Substitute
import SubstituteBaseStruct
import FreeNames
import DefinedNames
import FreeNamesProp()
import PropSyntax(HsDeclI,HsExpI,HsPatI,HsTypeI,HsQualTypeI,AssertionI,PredicateI,Rec(..))
import qualified PropSyntax as S
import PrettyPrint
import PrettySymbols
import TI hiding (Qual(..),Subst)
import TiDecorate(TiPat,DeclsUseType,no_use,specType,mapTiDeclsNames)
--import TiD(GetSigs(..),DeclInfo(..))
import TiProp()
import TiPropStruct
import TiBaseStruct(tcE,tcD)
import Lists((\\\))
import MUtils(( # ),mapSnd)
--import Maybe(mapMaybe)
--import IOExts(trace)

--------------------------------------------------------------------------------
type TiModule i = HsModuleI i (TiDecls i)
data TiDecls i = Decs [TiDecl i] (DeclsType i) deriving Show
newtype TiDecl i = Dec (DStruct i) deriving Show
newtype TiAssertion i = PA (PropPA i) deriving Show
newtype TiPredicate i = PP (PropPP i) deriving Show

-- Overloaded assertions:
data OTiAssertion i = OA [i] [(Typed i i,TiExp i)] (TiAssertion i) deriving Show

data TiExp i
  = Exp (EStruct i)
  | TiSpec (HsIdentI i) (Scheme i) [HsTypeI i] -- specialize a polymorphic identifier
  | TiTyped (TiExp i) (HsTypeI i) -- decorate expression with inferred type
  deriving Show

----

type DStruct i = PropDI i (TiExp i) (TiPat i) (TiDecls i) (HsTypeI i) [HsTypeI i] (HsTypeI i) (OTiAssertion i) (TiPredicate i)

type DBase i = DI i (TiExp i) (TiPat i) (TiDecls i) (HsTypeI i) [HsTypeI i] (HsTypeI i)
type EStruct i = EBase i
type EBase i = EI i (TiExp i) (TiPat i) (TiDecls i) (HsTypeI i) [HsTypeI i]

--type PropDecl i =  PropDI i (TiExp i) (HsPatI i) (TiDecls i) (HsTypeI i) [HsTypeI i] (HsTypeI i) (TiAssertion i) (TiPredicate i)
type PropPA i = PA i (TiExp i) (HsQualTypeI i) (TiAssertion i) (TiPredicate i)
type PropPP i = PP i (TiExp i) (HsPatI i) (HsQualTypeI i) (TiAssertion i) (TiPredicate i)

--------------------------------------------------------------------------------
instance Rec (TiDecl i) (DStruct i) where rec = Dec; struct (Dec d) = d
instance Rec (TiExp i) (EStruct i) where rec = Exp -- ; struct = ???
instance Rec (TiAssertion i) (PropPA i) where rec = PA; struct (PA pa) = pa
instance Rec (TiPredicate i) (PropPP i) where rec = PP; struct (PP pp) = pp
--------------------------------------------------------------------------------
instance MapExp (TiExp i) (TiDecl i) where mapExp = mapExpRec
instance MapExp (TiExp i) (TiAssertion i) where mapExp = mapExpRec
instance MapExp (TiExp i) (TiPredicate i) where mapExp = mapExpRec

instance MapExp (TiExp i) (TiDecls i) where
  mapExp f (Decs ds dt) = Decs (mapExp f ds) dt

instance Subst i (TiExp i) where
  subst s e =
    case e of
      Exp be -> substE' Exp s be
      TiTyped e t -> TiTyped (subst s e) t
      TiSpec (HsVar x) sc ts ->
          case isId sx of
            Just y -> TiSpec y sc ts
	    _ -> sx -- type annotation is lost!
	where sx = s x
      _ -> e 

instance MapExp (TiExp i) (OTiAssertion i) where
  mapExp f (OA is ds pa) = OA is (mapSnd f ds) (mapExp f pa)

--------------------------------------------------------------------------------

instance (ValueId i, TypeId i, Fresh i, PrintableOp i,HasSrcLoc i,TypedId PId i)
      => TypeCheckDecl i (HsDeclI i) (TiDecls i) where
  tcDecl bs = recprop (tcD bs) (tcPD bs)

instance AddDeclsType i (TiDecls i) where
  addDeclsType dt1 (Decs ds dt2) = Decs ds (dt1+++dt2)
  rmDeclsType (Decs ds dt2) = Decs ds ([],[])

instance (ValueId i, TypeId i, Fresh i, PrintableOp i,HasSrcLoc i,TypedId PId i)
      => TypeCheck i (HsExpI i) (Typed i (TiExp i)) where
  tc = tcE . struct 

instance (ValueId i, TypeId i, Fresh i, PrintableOp i,HasSrcLoc i,TypedId PId i)
      => TypeCheck i (AssertionI i) (Typed i (TiAssertion i)) where
  tc = tc . struct 

instance (ValueId i, TypeId i, Fresh i, PrintableOp i,HasSrcLoc i,TypedId PId i)
      => TypeCheck i (AssertionI i) (Typed i (OTiAssertion i)) where
  tc a = emap (OA [] []) # tc (struct a)

instance (ValueId i, TypeId i, Fresh i, PrintableOp i,HasSrcLoc i,TypedId PId i)
      => TypeCheck i (PredicateI i) (Typed i (TiPredicate i)) where
  tc = tc . struct 
{-
instance GetSigs i [Pred i] (Type i) (TiDecls i) where
  getSigs (Decs ds _) = mapMaybe getSig ds
    where
      getSig (Dec (Base (HsTypeSig s is c tp))) = Just (s,is,c,tp)
      getSig _                                  = Nothing
-}
instance (TypeVar i,ValueId i) => DeclInfo i (TiDecl i) where
  explicitlyTyped kenv tinfo bs  = prop e e . struct
    where e x = explicitlyTyped kenv tinfo bs x

instance DeclInfo i (TiDecls i)

--------------------------------------------------------------------------------

instance TypeVar i => EnvFrom (TiDecls i) (DeclsUseType i) where
  accEnv (Decs ds dt) = (no_use dt+++) . accEnv ds

instance TypeVar i => EnvFrom (TiDecl i) (DeclsUseType i) where
  accEnv = accEnv . struct

instance TypeVar i => EnvFrom (TiExp i) (DeclsUseType i) where
  accEnv (Exp e) = accEnv e
  accEnv (TiSpec v@(HsVar _) t as) = (([],[v:>:(t,specType t as)])+++)
  accEnv (TiTyped e t) = accEnv e
  accEnv _ = id


instance (EnvFrom b e,EnvFrom p e) => EnvFrom (Prop b p) e where
  accEnv = prop accEnv accEnv

instance EnvFrom (PD i pa pp) (DeclsUseType i) where accEnv = ignore -- hmm

ignore = const id

--------------------------------------------------------------------------------

--instance HasBaseStruct (TiDecls i) [TiDecl i] where base ds = Decs (base ds) ([],[])
instance HasBaseStruct (TiDecl i) (DBase i) where base    = Dec . base
instance GetBaseStruct (TiDecl i) (DBase i) where basestruct = basestruct . struct
instance HasBaseStruct (TiExp i) (EBase i)  where base    = Exp

instance HasPropStruct (TiDecl i) (PD i (OTiAssertion i) (TiPredicate i)) where
  proprec = rec . Prop

instance HasPropStruct (TiAssertion i) (PropPA i) where proprec = rec
instance HasPropStruct (TiPredicate i) (PropPP i) where proprec = rec

instance HasId i (TiExp i) where
  ident = Exp . ident
  isId (Exp e) = isId e
  isId (TiSpec x _ []) = Just x
  isId _ = Nothing --hmm

--instance HasLit (TiExp i) where lit = hsLit loc0
----instance HasLit (TiPat i) where lit = hsPLit

instance HasCoreSyntax i (TiExp i) where
  app = hsApp
  tuple = hsTuple
  list = hsList
--paren = hsParen

instance HasTypeApp i (TiExp i) where spec = TiSpec

instance HasTypeAnnot i (TiExp i) where typeAnnot = TiTyped

instance HasDef (TiDecls i) (TiDecl i) where
  nullDef (Decs ds _) = null ds
  noDef = Decs [] ([],[])
  consDef d (Decs ds ts) = Decs (d:ds) ts
  toDefs ds = Decs ds ([],[])
  appendDef (Decs ds1 ts1) (Decs ds2 ts2) = Decs (ds1++ds2) (ts1+++ts2)
  filterDefs p (Decs ds ts) = Decs (filter p ds) ts -- keep all type info?!

instance HasDefs (TiDecls i) (TiDecl i) where
  fromDefs (Decs ds _) = ds

instance HasSrcLoc (TiDecl i) where srcLoc (Dec d) = srcLoc d

instance HasAbstr i (TiDecl i) where abstract xs = mapRec (mapProp (abstract xs) (abstract xs))
instance HasAbstr i (TiDecls i) where abstract xs (Decs ds ti) = Decs (abstract xs ds) ti

--instance HasAbstr i (TiAssertion i) where
--  abstract is pa = foldr propLambda pa is

instance HasAbstr i (OTiAssertion i) where
  abstract is1 (OA is2 ds pa) = OA (is1++is2) ds pa

instance HasLocalDef i (TiExp i) (OTiAssertion i) where
  letvar it e (OA is ds pa) = OA is ((it,e):ds) pa

instance (HasAbstr i b, HasAbstr i p) => HasAbstr i (Prop b p) where
  abstract xs = mapProp (abstract xs) (abstract xs)

--------------------------------------------------------------------------------
instance DefinedNames i (TiDecls i) where definedNames (Decs ds ti) = definedNames ds
instance ClassMethods i (TiDecls i) where classMethods c cnt (Decs ds ti) = classMethods c cnt ds
instance MapDefinedNames i (TiDecls i) where
   mapDefinedNames f (Decs ds ti) = mapTiDeclsNames Decs f ds ti

instance DefinedNames i (TiDecl i) where definedNames = definedNamesRec
instance ClassMethods i (TiDecl i) where classMethods = classMethodsRec
instance ValueId i => AddName i (TiDecl i) where addName = addNameRec

instance MapDefinedNames i (TiDecl i) where
   mapDefinedNames = mapDefinedNamesRec

instance Eq i => FreeNames i (TiDecl i) where freeNames = freeNamesRec
instance Eq i => FreeNames i (TiAssertion i) where freeNames = freeNamesRec
instance Eq i => FreeNames i (TiPredicate i) where freeNames = freeNamesRec
instance Eq i => FreeNames i (TiDecls i) where freeNames (Decs ds ti) = freeNames ds
instance Eq i => FreeNames i (TiExp i) where
  freeNames (Exp e) = freeNames e
  freeNames (TiSpec x sc ts) = [val x] -- hmm
  freeNames (TiTyped e t) = freeNames e -- hmm

instance Eq i => FreeNames i (OTiAssertion i) where
  freeNames (OA is ds pa) = freeNames (es,pa,ts) \\\ map FreeNames.var (is++is2)
    where (tis,es) = unzip ds
	  is2:>:ts = unzipTyped tis
-------------------------------------------------------------------------------

instance Eq i => HasLocalDef i (TiExp i) (TiDecl i) where
   letvar x e = mapRec (mapProp (letvar x e) (letvar x e))

instance Eq i => HasLocalDef i (TiExp i) (TiDecls i) where
   letvar x e (Decs ds ts) = Decs (letvar x e ds) ts

instance TypeVar i => Types i (TiDecl i) where
  tmap f = mapRec (mapProp (tmap f) (mapPD id (tmap f) (tmap f)))
--tv = ...

instance TypeVar i => Types i (TiDecls i) where
  tmap f (Decs ds (ks,ts)) = Decs (tmap f ds) (ks,tmap f ts)
--tv = ...

instance TypeVar i => Types i (TiExp i) where
  tmap f (Exp e) = Exp (mapEI id (tmap f) (tmap f) (tmap f) id id e)
  tmap f (TiSpec x sch ts) = TiSpec x (tmap f sch) (tmap f ts)
  tmap f (TiTyped e t) = TiTyped (tmap f e) (f t)
--tv = ...

instance (Types i c,Types i t) => Types i (Q c t) where
  tmap f (c:=>t) = tmap f c:=>tmap f t

instance TypeVar i => Types i (TiAssertion i) where
  tmap f (PA pa) = PA (mapPA id (tmap f) (tmap f) (tmap f) (tmap f) pa)

instance TypeVar i => Types i (TiPredicate i) where
  tmap f (PP pp) = PP (mapPP id (tmap f) id (tmap f) (tmap f) (tmap f) pp)

instance TypeVar i => Types i (OTiAssertion i) where
  tmap f (OA is ds pa) = OA is (tmap f ds) (tmap f pa)

--------------------------------------------------------------------------------
instance (TypeId i,ValueId i,PrintableOp i) => Printable (TiDecl i) where
  ppi (Dec d)      = ppi d

instance (TypeId i,ValueId i,PrintableOp i) => Printable (TiDecls i) where
  ppi (Decs ds (ks,ts)) = vcat ds $$
			  ppIfTypeInfo (sep [ppi "{-",ppi ks,ppi ts,ppi "-}"])
  ppis (Decs ds ([],[])) = ppis ds
  ppis (Decs ds (ks,ts)) = ppis ds ++
                           map ppIfTypeInfo [ppi "{-",ppi ks,ppi ts,ppi "-}"]

instance (TypeId i,ValueId i,PrintableOp i) => Printable (TiExp i) where
   ppi (Exp e)      = ppi e
   ppi (TiSpec x _ []) = wrap x
   ppi (TiSpec x _ ts) = wrap x <> ppIfTypeInfo ("{-"<>fsep (map wrap ts)<>"-}")
   ppi (TiTyped e t) = e <> ppIfDebug ("{-"<>el<>t<>"-}")

   wrap (Exp e) = wrap e
   wrap e = ppi e

instance (TypeId i,ValueId i,PrintableOp i) => Printable (TiAssertion i) where
  ppi=ppi.struct
  wrap=wrap.struct

instance (TypeId i,ValueId i,PrintableOp i) => Printable (TiPredicate i) where
  ppi=ppi.struct
  wrap=wrap.struct

instance (TypeId i,ValueId i,PrintableOp i) => Printable (OTiAssertion i) where
  ppi (OA is ds pa) = ppLam is (ppLet ds (ppi pa))
   where
     ppLam [] d = d
     ppLam is d = sep [lambda<+>hsep is<+>rarrow,d]

     ppLet [] d = d
     ppLet ds d = sep ["let"<+>vcat (map ppD ds),"in"<+>d]

     ppD (it,e) = it<+>"="<+>e
