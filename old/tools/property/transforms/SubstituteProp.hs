module SubstituteProp where
import Recursive
import Substitute
import SubstitutePropStruct
import SubstituteBaseStruct
import PropSyntaxRec(HsExpI,HsDeclI,PredicateI,AssertionI)

instance MapExp (HsExpI i) (HsDeclI i)    where mapExp = mapExpRec
instance MapExp (HsExpI i) (PredicateI i) where mapExp = mapExpRec
instance MapExp (HsExpI i) (AssertionI i) where mapExp = mapExpRec
instance MapExp (HsExpI i) (HsExpI i)     where mapExp = mapExpRec

instance Subst i (HsExpI i) where subst s = substE s . struct
