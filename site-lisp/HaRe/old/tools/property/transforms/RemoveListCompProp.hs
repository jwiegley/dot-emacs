module RemoveListCompProp(rmAllListComp) where
import RemoveListComp
import Substitute
import SubstituteProp
import Recursive
import PropSyntaxRec(HsExpI)
import TiNames(ValueId)
import TiPropInstances() -- HasDef [HsDeclI i] (HsDeclI i)

instance ValueId i => RmListComp i (HsExpI i) where
  rmListComp cm = rmListCompE cm . struct
