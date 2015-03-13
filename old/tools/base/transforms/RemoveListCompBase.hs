module RemoveListCompBase where
import RemoveListComp
import Recursive
import SyntaxRec(HsExpI)
import TiNames(ValueId)
import TiBase() -- HasDef [HsDeclI i] (HsDeclI i)

instance ValueId i => RmListComp i (HsExpI i) where
  rmListComp cm = rmListCompE cm . struct
