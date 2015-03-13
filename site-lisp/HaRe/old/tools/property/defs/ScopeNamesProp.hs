module ScopeNamesProp where
import ScopeNames
import ScopeNamesPropStruct
import ScopeNamesBaseStruct
import ScopeNamesBase() -- instance for HsTypeI
import DefinedNamesProp()
import FreeNamesProp()
import PropSyntax
import MUtils

instance Eq i => ScopeNames i e (HsExpI i) (HsExpI (i,e)) where
   scopeNames = scopeNamesRec

instance Eq i => ScopeNames i e (HsDeclI i) (HsDeclI (i,e)) where
   scopeNames = scopeNamesRec

instance Eq i => ScopeNames i e (AssertionI i) (AssertionI (i,e)) where
   scopeNames = scopeNamesRec

instance Eq i => ScopeNames i e (PredicateI i) (PredicateI (i,e)) where
   scopeNames = scopeNamesRec

instance (ScopeNames i e b1 b2,ScopeNames i e p1 p2)
      => ScopeNames i e (Prop b1 p1) (Prop b2 p2) where
  scopeNames ext p = mapMProp sc sc p
    where sc x = scopeNames ext x

---

instance (ScopeNames i e c1 c2,ScopeNames i e t1 t2)
      => ScopeNames i e (Q c1 t1) (Q c2 t2) where
  scopeNames ext (c:=>t) = (:=>) # sc c <# sc t
     where sc x = scopeNames ext x
