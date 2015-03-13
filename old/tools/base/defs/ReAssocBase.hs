module ReAssocBase(module ReAssocBase,module ReAssoc) where
import Syntax(HsExpI,HsPatI,HsDeclI,HsIdentI(..))
import ReAssoc
import ReAssocBaseStruct()
import DefinedNamesBase()
import Recursive
import HasBaseStruct(hsInfixApp,hsPInfixApp)

{-
Knot-tying definitions for the base syntax
-}

instance Eq i => ReAssoc i (HsExpI  i) where reAssoc = reAssocRec
instance Eq i => ReAssoc i (HsPatI  i) where reAssoc = reAssocRec
instance Eq i => ReAssoc i (HsDeclI i) where reAssoc = reAssocRec

instance HasInfixDecls i (HsDeclI i)   where getInfixDecls = getInfixDeclsRec

instance HasInfixApp i (HsExpI i) (HsExpI i) where
  infixApp = hsInfixApp
  isInfixApp = isInfixApp . struct

instance HasInfixApp i (HsPatI i) (HsPatI i) where
  infixApp p1 (HsCon c) p2 = hsPInfixApp p1 c p2
  isInfixApp = isInfixApp . struct
