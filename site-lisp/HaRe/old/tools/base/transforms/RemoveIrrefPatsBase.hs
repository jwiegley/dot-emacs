module RemoveIrrefPatsBase
    ( module RemoveIrrefPatsBase
    , module RemoveIrrefPats
    ) where

import RemoveIrrefPats
import RemoveIrrefPatsBaseStruct
import Syntax
--import TiClasses(HasDef(..))
import TiBase()

instance RemIrrefPats (HsDeclI i) (OM i [HsDeclI i]) 
                                        where remIrrefPats = remIrrefPatsRec
instance RemIrrefPats (HsExpI i) (EM i) where remIrrefPats = remIrrefPatsRec
instance RemIrrefPats (HsPatI i) (OEM i (HsDeclI i)) 
                                        where remIrrefPats = remIrrefPatsRec


