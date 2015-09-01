module Names (module Names, module QualNames) where

import PosName(Id,HsName)
import HsName(ModuleName)
import QualNames
import SpecialNames()   -- for the instances


-- Interface of the module system, to the concrete type of names 


type Name     = Id
type ModName  = ModuleName
type QName    = HsName
