module ScopeHaskellProgram where
import ScopeProgram(scopeProgram)
import ScopeNamesBase()
import NameMapsBase()

import ParsedSyntax(Src)
import Syntax
import WorkModule
import ScopeProgram

scopeHaskellProgram = scopeProgram
  :: (Mss (Src HsName),WMs) -> IO (Mss (PN HsName),WMs)

type Mss i =[[HsModuleI (Src HsName) [HsDeclI i]]]
type WMs = [(ModuleName,WorkModuleI (Src HsName) (Src Id))]
