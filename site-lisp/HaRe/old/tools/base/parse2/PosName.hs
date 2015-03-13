module PosName(module PosName,ModuleName,HsIdentI(..)) where
import SourceNames
import qualified HsName as Hs
import HsIdent

type ModuleName = SN Hs.ModuleName
type HsName = SN Hs.HsName
type Id = SN Hs.Id
type HsIdent = HsIdentI HsName
