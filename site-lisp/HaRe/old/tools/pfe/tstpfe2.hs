import System(getArgs)

import HsParser(parse)
import ReAssocBase()
import FreeNamesBase()
import PPModules()

import Pfe2Cmds(pfe2)

main = pfe2 parse =<< getArgs
