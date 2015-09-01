module SubstituteBase where
import SubstituteBaseStruct
import Substitute
import Recursive
import Syntax

instance Subst i (HsExpI i) where subst s = substE s . struct

instance MapExp (HsExpI i) (HsDeclI i) where mapExp = mapExpRec
instance MapExp (HsExpI i) (HsExpI i)  where mapExp = mapExpRec

--instance MapExp e ds => MapExp (HsModuleI i ds) where ...
