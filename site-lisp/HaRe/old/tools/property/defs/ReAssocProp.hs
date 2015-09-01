module ReAssocProp where
import HsAssoc
import ReAssoc
import ReAssocPropStruct
import ReAssocBaseStruct
import DefinedNamesProp
import PropSyntax
import HasBaseStruct
import ReAssocBase()

-- The property extension doesn't add any new kinds of infix declarations,
-- so it is enough to extract the ones in the base syntax.
instance HasInfixDecls i (HsDeclI i) where
  getInfixDecls = maybe emptyOE getInfixDecls . basestruct

instance Eq i => ReAssoc i (HsDeclI i)    where reAssoc = pReAssoc
instance Eq i => ReAssoc i (HsExpI i)     where reAssoc = reAssocRec
instance Eq i => ReAssoc i (AssertionI i) where reAssoc = reAssocRec
instance Eq i => ReAssoc i (PredicateI i) where reAssoc = reAssocRec

instance HasInfixApp i (HsExpI i) (HsExpI i) where
  infixApp e1 op e2 = base $ infixApp e1 op e2
  isInfixApp = isInfixApp . struct

pReAssoc env = mapRec $ mapProp (reAssoc env) (reAssoc env)
