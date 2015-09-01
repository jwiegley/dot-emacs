import System(getArgs)

import HsParser(parse)

-- moved to PFe3Cmds
--import DefinedNamesBase()
-- import FreeNamesBase()
-- import ScopeNamesBase()
-- import NameMapsBase()
-- import ReAssocBase()
-- import MapDeclMBase()

import Pfe3Cmds(pfe3)
import PPU(getPPopts)


-- main = pfe3 parse =<< getArgs
main = pfe3 parse =<< getPPopts
