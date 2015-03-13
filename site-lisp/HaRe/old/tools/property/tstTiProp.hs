
import PropParser(parse)
import HsName(HsName)
import HsModule(HsModuleI)
import PropSyntax(HsModuleR)
import ScopeNamesProp()
import NameMapsProp()
import TiHsName
import ReAssocProp()
import TiPropDecorate
import PrettyPrint
import UTF8Util
import System(getArgs)
import TiProgram
import MUtils
import DirUtils

main = (tstTi =<< expand =<< getArgs) `catch` utf8err


tstTi files =
  putStrLn =<< (utf8.(++("\n"++happy)).pp.r.fst # tcProgramFiles parse files)

r = id :: I [[HsModuleI i1 (TiDecls i2)]]

type I a = a->a
