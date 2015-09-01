{-+
This module provides type inference for the base syntax.
This type checker outputs an abstract syntax tree where all declaration lists
have been decorated with the kinds and types of the entities defined in
the list, and all applications of polymorphic functions have been decorated
with the instantiation of the quantified variables.
-}
module TiDecorate where
import BaseSyntax
import HasBaseStruct
import Substitute
import SubstituteBaseStruct(substE') --hmm
import FreeNames
import DefinedNames
import Syntax(HsPatI,HsTypeI,HsDeclI,HsExpI,Rec(..))
import qualified Syntax as S
import PrettyPrint
import PrettySymbols
import TI hiding (Subst)
import TiBase()
import TiBaseStruct(tcE,tcP,tcD)
import Data.List(nub)
--import Maybe(mapMaybe)
--import QualNames
import MUtils(apSnd)
--import IOExts(trace)

--------------------------------------------------------------------------------
--type TiModule i = HsModuleI i (TiDecls i)
data TiDecls i = Decs [TiDecl i] (DeclsType i) deriving Show

type DStruct i = DI i (TiExp i) (TiPat i) (TiDecls i) (HsTypeI i) [HsTypeI i] (HsTypeI i)
type EStruct i = EI i (TiExp i) (TiPat i) (TiDecls i) (HsTypeI i) [HsTypeI i]
type PStruct i = PI i (TiPat i)

newtype TiDecl i = Dec (DStruct i) deriving Show

data TiExp i
  = Exp (EStruct i)
  | TiSpec (HsIdentI i) (Scheme i) [HsTypeI i] -- specialize a polymorphic identifier
  | TiTyped (TiExp i) (HsTypeI i)
  deriving Show

data TiPat i
  = Pat (PStruct i)
  | TiPApp (TiPat i) (TiPat i) -- for fromInteger & fromRational & n+k
  | TiPSpec (HsIdentI i) (Scheme i) [HsTypeI i] -- specialize a polymorphic identifier
  | TiPTyped (TiPat i) (HsTypeI i)
  deriving Show

--------------------------------------------------------------------------------
instance MapExp (TiExp i) (TiDecls i) where
  mapExp f (Decs ds dt) = Decs (mapExp f ds) dt

instance MapExp (TiExp i) (TiDecl i) where mapExp = mapExpRec

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
--------------------------------------------------------------------------------

instance (PrintableOp i,ValueId i,TypeId i,Fresh i,HasSrcLoc i,TypedId PId i)
      => TypeCheckDecl i (HsDeclI i) (TiDecls i) where
  tcDecl bs = tcD bs . struct

instance AddDeclsType i (TiDecls i) where
  addDeclsType dt1 (Decs ds dt2) = Decs ds (dt1+++dt2)
  rmDeclsType (Decs ds dt) = Decs ds ([],[])

instance (PrintableOp i,ValueId i,TypeId i,Fresh i,HasSrcLoc i,TypedId PId i)
      =>  TypeCheck i (HsExpI i) (Typed i (TiExp i)) where tc (S.Exp e) = tcE e

instance (Printable i,ValueId i,TypeId i,Fresh i)
      =>  TypeCheck i (HsPatI i) (Typed i (TiPat i)) where tc (S.Pat e) = tcP e
{-
instance GetSigs i [Pred i] (Type i) (TiDecls i) where
  getSigs (Decs ds _) = mapMaybe getSig ds
    where
      getSig (Dec (HsTypeSig s is c tp)) = Just (s,is,c,tp)
      getSig _                    = Nothing

instance (TypeVar i,ValueId i) => DeclInfo i (TiDecl i) where
  explicitlyTyped {-m-} bs = explicitlyTyped {-m-} bs . struct
  isUnrestricted b = isUnrestricted b . struct

instance DeclInfo i (TiDecls i)
-}
--------------------------------------------------------------------------------

type DeclsUseType i = ([TAssump i],[UAssump i])
type UAssump i = Typing (HsIdentI i) (Scheme i,Maybe (Type i))

instance EnvFrom ds env => EnvFrom (HsModuleI m i ds) env where
  accEnv = accEnv . hsModDecls

instance TypeVar i => EnvFrom (TiDecls i) (DeclsUseType i) where
  accEnv (Decs ds dt) = (no_use dt+++) . accEnv ds

no_use = apSnd ((map.fmap) (flip (,) Nothing))
drop_use = apSnd ((map.fmap) fst)

instance TypeVar i => EnvFrom (TiDecl i) (DeclsUseType i) where
  accEnv = accEnv . struct

instance (EnvFrom e env,EnvFrom p env,EnvFrom ds env)
      => EnvFrom (DI i e p ds t c tp) env where
  accEnv = accDI ignore accEnv accEnv accEnv ignore ignore ignore

instance TypeVar i => EnvFrom (TiPat i) (DeclsUseType i) where
  accEnv (Pat p) = accEnv p
  accEnv (TiPSpec v@(HsVar _) t as) = (([],[v:>:(t,specType t as)])+++)
  accEnv (TiPApp (TiPSpec {}) p2) = accEnv p2
  accEnv (TiPApp p1 p2) = accEnv p1 . accEnv p2
  accEnv (TiPTyped p t) = accEnv p
  accEnv _ = id

instance EnvFrom p env => EnvFrom (PI i p) env where
  accEnv = accPI ignore accEnv

instance TypeVar i => EnvFrom (TiExp i) (DeclsUseType i) where
  accEnv (Exp e) = accEnv e
  accEnv (TiSpec v@(HsVar _) t as) = (([],[v:>:(t,specType t as)])+++)
  accEnv (TiTyped e t) = accEnv e
  accEnv _ = id

specType (Forall _ kgs (_:=>t)) as =
    if map tyvar gs==as
    then Nothing
    else Just (apply s t)
  where s = S (zip gs as)
        gs = tdom kgs

instance (EnvFrom e env,EnvFrom p env,EnvFrom ds env)
      => EnvFrom (EI i e p ds t c) env where
  accEnv = accEI ignore accEnv accEnv accEnv ignore ignore

ignore = const id

--------------------------------------------------------------------------------
instance HasBaseStruct (TiDecls i) [TiDecl i] where base ds = Decs ds ([],[])
instance HasBaseStruct (TiDecl i) (DStruct i) where base    = Dec
instance HasBaseStruct (TiExp i) (EStruct i)  where base    = Exp
instance HasBaseStruct (TiPat i) (PStruct i)  where base    = Pat

instance Rec (TiDecl i) (DStruct i) where r = base; struct (Dec d) = d
instance GetBaseStruct (TiDecl i) (DStruct i) where basestruct = Just . struct

instance HasId i (TiExp i) where
  ident = Exp . ident
  isId (Exp e) = isId e
  isId (TiSpec x _ []) = Just x
  isId _ = Nothing --hmm

instance HasId i (TiPat i) where
  ident = Pat . ident
  isId (Pat e) = isId e
  isId (TiPSpec x _ []) = Just x
  isId _ = Nothing --hmm

--instance HasLit (TiExp i) where lit = hsLit loc0
--instance HasLit (TiPat i) where lit = hsPLit loc0

instance HasCoreSyntax i (TiExp i) where
  app = hsApp
  tuple = hsTuple
  list = hsList
--paren = hsParen

instance HasCoreSyntax i (TiPat i) where
  app = TiPApp
  tuple = hsPTuple loc0 -- !!
  list = hsPList loc0 -- !!
--paren = hsParen

instance HasTypeApp i (TiExp i) where spec=TiSpec
instance HasTypeApp i (TiPat i) where spec=TiPSpec

instance HasTypeAnnot i (TiExp i) where typeAnnot=TiTyped
instance HasTypeAnnot i (TiPat i) where typeAnnot=TiPTyped

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

instance HasAbstr i (TiDecl i) where abstract xs (Dec d)      = Dec (abstract xs d)
instance HasAbstr i (TiDecls i) where abstract xs (Decs ds ti) = Decs (abstract xs ds) ti
--------------------------------------------------------------------------------
instance DefinedNames i (TiDecls i) where definedNames (Decs ds ti) = definedNames ds
instance ClassMethods i (TiDecls i) where classMethods i cnt (Decs ds ti) = classMethods i cnt ds
instance MapDefinedNames i (TiDecls i) where
   mapDefinedNames f (Decs ds ti) = mapTiDeclsNames Decs f ds ti

mapTiDeclsNames decs f ds (ks,ts) =
      decs (mapDefinedNames f ds) (ks,mapVars f ts)
   where mapVars f = map $ emap $ mapHsIdent2 f id

instance DefinedNames i (TiDecl i) where definedNames = definedNamesRec
instance ClassMethods i (TiDecl i) where classMethods = classMethodsRec
instance AddName i (TiDecl i)

instance MapDefinedNames i (TiDecl i) where
   mapDefinedNames = mapDefinedNamesRec

instance DefinedNames i (TiPat i) where
  definedNames (Pat p) = definedNames p
  definedNames (TiPSpec (HsVar x) sc ts) = [value x]
  definedNames (TiPSpec _ sc ts) = []
  definedNames (TiPTyped p t) = definedNames p
  definedNames (TiPApp p1 p2) = appDef p1 [p2]
    where
      appDef (TiPApp p1 p2) ps = appDef p1 (p2:ps)
      appDef (TiPSpec c@(HsCon _) sc ts) ps = definedNames ps
      appDef (TiPSpec x sc ts) ps = [] -- overloaded literal, binds nothing

instance MapDefinedNames i (TiPat i) where
  mapDefinedNames f p =
    case p of
      Pat p -> Pat (m p)
      TiPSpec (HsVar x) sc ts -> TiPSpec (HsVar (f x)) sc ts
      TiPTyped p t -> TiPTyped (m p) t
      TiPApp p1 p2 -> mApp p1 [p2]
    where
      m x = mapDefinedNames f x

      mApp (TiPApp p1 p2) ps = mApp p1 (p2:ps)
      mApp p@(TiPSpec c@(HsCon _) _ _) ps = apps (p:m ps)
      mApp p ps = apps (p:ps) -- overloaded literal, binds nothing

      apps = foldl1 TiPApp

instance Eq i => FreeNames i (TiDecl i) where freeNames = freeNamesRec
instance Eq i => FreeNames i (TiDecls i) where freeNames (Decs ds ti) = freeNames ds
instance Eq i => FreeNames i (TiExp i) where
  freeNames (Exp e) = freeNames e
  freeNames (TiSpec x sc ts) = [val x] -- hmm
  freeNames (TiTyped e t) = freeNames e -- hmm

instance (Eq i) => FreeNames i (TiPat i) where
  freeNames (Pat p) = freeNames p
  freeNames (TiPSpec (HsCon c) sc ts) = [FreeNames.con c]
  freeNames (TiPSpec _ sc ts) = []
  freeNames (TiPTyped p t) = freeNames p -- hmm
  freeNames p@(TiPApp p1 p2) = appFree p1 [p2]
    where
      {- An application is either
           1. A construtor applied to a number of subpatterns, or
           2. fromInteger/fromRational/negate, applied to a dictionary
              and a literal. -}
      appFree (TiPApp p1 p2) ps = appFree p1 (p2:ps)
      appFree (TiPSpec (HsCon c) sc ts) ps = nub (FreeNames.con c:freeNames ps)
      appFree (TiPSpec x sc ts) ps = nub (val x:concatMap argFree ps)
	   -- x must be negate, fromInteger or fromRational
      appFree (Pat (HsPId x@(HsVar _))) [] = [] -- dictionary bound in where clause
      appFree (Pat (HsPId _)) ps = error "Bug: TiDecorate.appFree (Pat (HsPId _))"
      appFree (Pat p) ps = error ("Bug: TiDecorate.appFree (Pat _)")
      appFree p ps = error ("Bug: TiDecorate.appFree p ps")

      argFree (Pat (HsPLit _ _)) = []
      argFree p = appFree p []

--------------------------------------------------------------------------------
instance Eq i => HasLocalDef i (TiExp i) (TiDecl i) where
   --letvar x e (Dec d) = Dec (letvar x e d)
    letvar x e = mapRec (letvar x e)

instance Eq i => HasLocalDef i (TiExp i) (TiDecls i) where
   letvar x e (Decs ds ts) = Decs (letvar x e ds) ts

-- For these instances, tmap f should apply f to all types inserted during
-- type checking, since they might contain type variables that have been
-- instantiated later.
instance TypeVar i => Types i (TiDecl i) where
  tmap f (Dec d) = Dec (tmap f d)
--tv = ...

instance TypeVar i => Types i (TiDecls i) where
  tmap f (Decs ds (ks,ts)) = Decs (tmap f ds) (ks,tmap f ts)
--tv = ...

instance TypeVar i => Types i (TiExp i) where
  tmap f (Exp e) = Exp (mapEI id (tmap f) (tmap f) (tmap f) id id e)
  tmap f (TiSpec x sc ts) = TiSpec x (tmap f sc) (tmap f ts)
  tmap f (TiTyped e t) = TiTyped (tmap f e) (f t)
--tv = ...

instance TypeVar i => Types i (TiPat i) where
  tmap f (Pat p) = Pat (mapPI id (tmap f) p)
  tmap f (TiPApp p1 p2) = TiPApp (tmap f p1) (tmap f p2)
  tmap f (TiPSpec x sc ts) = TiPSpec x (tmap f sc) (tmap f ts)
  tmap f (TiPTyped e t) = TiPTyped (tmap f e) (f t)
--tv = ...
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
   ppi (TiSpec x sc []) = wrap x <> ppIfDebug ("{-"<>sc<>"-}")
   ppi (TiSpec x sc ts) = wrap x <>
                          ppIfDebug ("{-"<>sc<>"@"<>fsep (map wrap ts)<>"-}")
   ppi (TiTyped e t) = e <> ppIfDebug ("{-"<>el<>t<>"-}")

   wrap (Exp e) = wrap e
   wrap e = ppi e


instance (TypeId i,ValueId i,PrintableOp i) => Printable (TiPat i) where
   ppi (Pat e)      = ppi e
   ppi (TiPSpec x sc []) = wrap x <> ppIfDebug ("{-"<>sc<>"-}")
   ppi (TiPSpec x sc ts) = wrap x <> ppIfTypeInfo ("{-"<>ppIfDebug (sc<>"@")<>fsep (map wrap ts)<>"-}")
   ppi (TiPApp p1 p2) = fsep [ ppi p1, letNest (wrap p2) ]
   ppi (TiPTyped p t) = p<>ppIfDebug ("{-"<>el<>t<>"-}")

   wrap (Pat e) = wrap e
   wrap p@(TiPApp {}) = parens (ppi p)
   wrap p = ppi p
