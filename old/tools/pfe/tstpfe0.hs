import System(getArgs)

import HsParser(parse)
import ReAssocBase()
--import NameMapsBase()
--import FreeNamesBase()

import Pfe0Cmds(pfe0)

main = pfe0 parse =<< getArgs
