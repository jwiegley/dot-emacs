module TiNameMaps(module TiNameMaps,AccNames(..)) where
import Data.List(nub)

import NameMaps(AccNames(..))
import TypedIds(IdTy(..),TypeInfo(..),idTy)
import HsIdent(HsIdentI(..))

allTypeNames ds = nub (accNames typeName ds [])
  where
    typeName x =
      case idTy x of
        Class {}                       -> (HsCon x:)
	Type TypeInfo{defType=Nothing} -> (HsVar x:)
	Type {}                        -> (HsCon x:)
	_ -> id    
