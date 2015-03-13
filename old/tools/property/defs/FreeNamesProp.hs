module FreeNamesProp where
import PropSyntax
import FreeNames
import FreeNamesPropStruct
import FreeNamesBase
import DefinedNamesProp

instance Eq i => FreeNames i (HsDeclI i)    where freeNames = freeNamesRec
instance Eq i => FreeNames i (HsExpI i)     where freeNames = freeNamesRec
instance Eq i => FreeNames i (AssertionI i) where freeNames = freeNamesRec
instance Eq i => FreeNames i (PredicateI i) where freeNames = freeNamesRec

instance (FreeNames i b,FreeNames i p) => FreeNames i (Prop b p) where
 freeNames = prop freeNames freeNames
