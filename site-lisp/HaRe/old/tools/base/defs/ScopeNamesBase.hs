module ScopeNamesBase where
import ScopeNames
import ScopeNamesBaseStruct
import DefinedNamesBase()
import FreeNamesBase()
import Syntax

instance Eq i => ScopeNames i e (HsExpI i) (HsExpI (i,e)) where
   scopeNames = scopeNamesRec

instance Eq i => ScopeNames i e (HsDeclI i) (HsDeclI (i,e)) where
   scopeNames = scopeNamesRec

instance ScopeNames i e (HsPatI i) (HsPatI (i,e)) where
   scopeNames = scopeNamesRec

instance ScopeNames i e (HsTypeI i) (HsTypeI (i,e)) where
   scopeNames = scopeNamesRec


