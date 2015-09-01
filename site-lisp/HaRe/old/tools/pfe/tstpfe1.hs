import System(getArgs)

import HsParser(parse)
import ReAssocBase()
import FreeNamesBase()
import PPModules()

import Pfe1Cmds(pfe1)

main = pfe1 parse =<< getArgs
