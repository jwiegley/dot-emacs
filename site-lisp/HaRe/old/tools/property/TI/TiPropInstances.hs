{-+
The various auxiliary operations required by the extensible type checker
are defined here.
-}
module TiPropInstances where
import List(partition)
import Maybe(isJust)
--import Maybe(mapMaybe)

import HasBaseStruct
import PropSyntax
import TI hiding (Subst,Qual(..))
--import TiD(DeclInfo(..),HasMethodSigs(..))
--import TiHsName
--import TiBaseStruct(pApp)
import TiBase()
--import TiPrelude(pt)
import HsPropStruct
import MUtils
import DefinedNamesProp()
import FreeNamesProp()
import Substitute
import SubstituteProp

instance HasId i (HsExpI i) where
  ident = base . ident
  isId = isId @@ basestruct

--instance HasLit (HsExpI i) where lit = hsLit loc0
----instance HasLit (HsPatI i) where lit = hsPLit

instance HasCoreSyntax i (HsExpI i) where
  app e1 e2 = hsApp e1 e2
  tuple = hsTuple
  list = hsList

instance HasAbstr i (HsExpI i) where
  abstract = hsLambda . map var
{-
instance HasId i (HsPatI i) where
  ident = base . ident
  isId = isId @@ basestruct

instance HasCoreSyntax i (HsPatI i) where
  app (Pat (Base p1)) p2 = base $ pApp p1 p2 -- hmm
  tuple = hsPTuple
  list = hsPList
-}

instance HasAbstr i (HsDeclI i) where
  abstract is = mapRec (mapProp (abstract is) id) -- !!

instance HasAbstr i pa => HasAbstr i (PD i pa pp) where
  abstract is pd =
    case pd of
      HsAssertion s optn pa -> HsAssertion s optn (abstract is pa)
      HsPropDecl s n ns pp -> HsPropDecl s n (map HsVar is++ns) pp

--instance HasAbstr i (AssertionI i) where
--  abstract is pa = foldr propLambda pa is

instance Eq i => HasLocalDef i (HsExpI i) (HsDeclI i) where
  letvar xt e = mapRec (mapProp (letvar xt e) id) -- !!

instance (FreeNames i pa,MapExp e pa,HasAbstr i pa,
	  HasLocalDef i e pa,
	  FreeNames i pp,MapExp e pp,
	  HasId i e,Subst i e)
      => HasLocalDef i e (PD i pa pp) where
  letvar xt@(i:>:t) e pd =
    case pd of
      HsPropDecl s n ns pp ->
	  if HsVar i `elem` freeVars pp
          then if isJust (isId e)
	       then HsPropDecl s n ns (esubst1 var e i pp)
	       else --pd -- hmm!!
                    HsPropDecl s n ns (esubst1 var e i pp) --code duplication...
                    
	  else pd
      HsAssertion s optn pa -> 
	  if HsVar i `elem` freeVars pa
          then if isJust (isId e)
	       then HsAssertion s optn (esubst1 var e i pa)
	       else HsAssertion s optn (letvar xt e pa)
	  else pd

instance AddDeclsType i [HsDeclI i]

instance HasDef [HsDeclI i] (HsDeclI i) where
  nullDef = null
  noDef = []
  consDef = (:)
  appendDef = (++)
  toDefs = id
  filterDefs = filter

instance (ValueId i,TypeVar i) => DeclInfo i (HsDeclI i) where
  explicitlyTyped kenv tinfo ctx =
      recprop (explicitlyTyped kenv tinfo ctx) (explicitlyTyped kenv tinfo ctx)
  --isTypeDecl = isBase isTypeDecl . struct
  isUnrestricted expl = recprop (isUnrestricted expl) (isUnrestricted expl)
  keepAmbigTypes = recprop keepAmbigTypes keepAmbigTypes

instance DeclInfo i (PD i pa pp) where
  explicitlyTyped _ _ _ pd =
    case pd of
      --HsAssertion s (Just n) pa -> ([],[HsCon n:>:mono (pt "Prop")])
      _ -> ([],[]) -- no explitit type info here...
  isUnrestricted _ _ = True
  keepAmbigTypes pd =
    case pd of
      HsAssertion {} -> True
      _ -> False


--- Dummy instances ---
-- Need something sensible when decorating the syntax tree with types...
instance TypeVar i => Types i (HsDeclI i)    where tmap f = id; tv d = []
instance TypeVar i => Types i (AssertionI i) where tmap f = id; tv d = []
instance TypeVar i => Types i (PredicateI i) where tmap f = id; tv d = []

instance HasTypeApp i (HsExpI i) where spec x _ ts = ident x
--instance HasTypeApp i (HsPatI i) where spec x _ ts = ident x

instance HasTypeAnnot i (HsExpI i)

instance HasMethodSigs [HsDeclI i] where
  splitMethodSigs = partition isSig
    where
      isSig (Dec (Base (HsTypeSig {}))) = True
      --isSig (Dec (Prop (HsAssertion _ (Just _) _))) = True
      isSig _                           = False
{-
instance GetSigs i [Pred i] (Type i) [HsDeclI i] where
  getSigs = mapMaybe getSig
    where
      getSig (Dec (Base (HsTypeSig s is c tp))) = Just (s,is,c,tp)
      getSig _                                  = Nothing
-}
