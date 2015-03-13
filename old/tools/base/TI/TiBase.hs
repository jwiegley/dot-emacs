{-
This module provides type inference for the base syntax.
Here, you will find only the knot-tying top-level definitions.
-}
module TiBase(Typing,Scheme{-,GetSigs(..),DeclInfo(..)-}) where
import Syntax hiding (extend)
import SubstituteBase()
import NameMapsBase() -- instance AccNames i (HsDeclI i)
import TI
--import QualNames
import TiBaseStruct
--import TiModule(tcModule)
import TiDs()
--import MUtils
import PrettyPrint
import Data.List(partition)
--import Maybe(mapMaybe)

--tstTcModule kbs tbs =
--  run emptyEnv . extendk kbs . extend tbs . getSubst . tcModule

instance (TypeId i,ValueId i,PrintableOp i,Fresh i,HasSrcLoc i,TypedId PId i)
      => TypeCheckDecl i (HsDeclI i) [HsDeclI i] where
  tcDecl bs = tcD bs . struct

instance Eq i => CheckRecursion i (HsDeclI i) where
    checkRecursion ds = checkTypeSynRec ds >> checkClassRec ds

instance HasMethodSigs [HsDeclI i] where
  splitMethodSigs = partition isSig
    where
      isSig (Dec (HsTypeSig {})) = True
      isSig _                    = False
{-
instance GetSigs i [Pred i] (Type i) [HsDeclI i] where
  getSigs = mapMaybe getSig
    where
      getSig (Dec (HsTypeSig s is c tp)) = Just (s,is,c,tp)
      getSig _                           = Nothing
-}
instance (Fresh i,TypeId i,ValueId i,PrintableOp i,HasSrcLoc i,TypedId PId i)
      => TypeCheck i (HsExpI i) (Typed i (HsExpI i)) where tc (Exp e) = tcE e
instance (Fresh i,TypeId i,ValueId i)
      => TypeCheck i (HsPatI i) (Typed i (HsPatI i)) where tc (Pat p) = tcP p

instance (ValueId i,TypeVar i) => DeclInfo i (HsDeclI i) where
  --explicitlyTyped m c = explicitlyTyped m c . struct
  explicitlyTyped ks tinfo c = explicitlyTyped ks tinfo c . struct
  --isTypeDecl = isTypeDecl . struct
  isUnrestricted expl = isUnrestricted expl . struct

instance HasAbstr i (HsDeclI i) where abstract xs = mapRec (abstract xs)
instance HasAbstr i (HsExpI i)  where abstract xs = mapRec (abstract xs)
instance Eq i => HasLocalDef i (HsExpI i) (HsDeclI i) where letvar x e = mapRec (letvar x e)
--instance ({-ValueId i,-}TypeVar i) => KindCheck i (HsDeclI i) () where kc = kc . struct
instance TypeVar i => KindCheck i (HsDeclI i) () where kc = kc . struct

instance HasId i (HsPatI i) where ident = r . ident; isId = isId . struct
instance HasId i (HsExpI i) where ident = r . ident; isId = isId . struct

--instance HasLit (SrcLoc->HsExpI i) where lit = flip hsLit
--instance HasLit (SrcLoc->HsPatI i) where lit = flip hsPLit

instance HasCoreSyntax i (HsPatI i) where
  app (Pat p1) p2 = r $ pApp p1 p2
  tuple = hsPTuple loc0 -- !! loc0
  list = hsPList loc0 -- !! loc0
--paren = hsPParen


instance HasCoreSyntax i (HsExpI i) where
  app = hsApp
  tuple = hsTuple
  list = hsList
--paren = hsParen

instance HasTypeApp i (HsExpI i) --where spec x sc ts = ident x
instance HasTypeApp i (HsPatI i) --where spec x sc ts = ident x

instance HasTypeAnnot i (HsExpI i)
instance HasTypeAnnot i (HsPatI i)

instance HasDef [HsDeclI i] (HsDeclI i) where
  nullDef = null
  consDef = (:); noDef = []; appendDef = (++); toDefs = id
  filterDefs = filter

instance TypeVar i => Types i (HsDeclI i) where
  tmap f = id
  tv d = []

instance AddDeclsType i [HsDeclI i] where addDeclsType dt = id
