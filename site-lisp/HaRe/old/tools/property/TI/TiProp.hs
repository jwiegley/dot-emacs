module TiProp where
import PropSyntax
import TI
--import TiBaseStruct
import FreeNamesProp
import DefinedNamesProp
import NameMapsProp
import TiPropStruct(tcPD,checkPredicateRec)
import TiBaseStruct(tcE,tcD,checkTypeSynRec,checkClassRec)
import TiPropInstances
import PrettyPrint
--import MUtils(( # ))

instance (TypeId i,ValueId i,PrintableOp i,Fresh i,HasSrcLoc i,TypedId PId i)
      => TypeCheckDecl i (HsDeclI i) [HsDeclI i] where
  tcDecl bs = recprop (tcD bs) (tcPD bs)

instance Eq i => CheckRecursion i (HsDeclI i) where
  checkRecursion ds = do checkTypeSynRec ds
			 checkClassRec ds
		         checkPredicateRec ds

instance (TypeId i,ValueId i,PrintableOp i,Fresh i,HasSrcLoc i,TypedId PId i)
      => TypeCheck i (HsExpI i) (Typed i (HsExpI i)) where
  tc (Exp e) = tcE e

instance (TypeId i,ValueId i,PrintableOp i,Fresh i,HasSrcLoc i,TypedId PId i)
      => TypeCheck i (AssertionI i) (Typed i (AssertionI i)) where
  tc (PA e) = tc e

instance (TypeId i,ValueId i,PrintableOp i,Fresh i,HasSrcLoc i,TypedId PId i)
      => TypeCheck i (PredicateI i) (Typed i (PredicateI i)) where
  tc (PP e) = tc e

instance ({-ValueId i,-}TypeVar i) => KindCheck i (HsDeclI i) () where
  kc = recprop kc kcPD
    where kcPD _ = return () -- hmm
