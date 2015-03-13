module SCMs where

import OpTypes
import NewSCC
--import Assoc
import Data.List(find)
--import Maybe(fromMaybe)
import Data.Maybe(mapMaybe)
import HsModule




hsModulesToGraph mods   = mods `zip` vals
    where
    vals        = (mapMaybe (lkpInMods . hsImpFrom) . hsModImports) `map` mods
    lkpInMods x = --fromMaybe (error $  "Missing module: "++show x) $
		  find ((== x) . hsModName) mods


scMods ms = map (map fst) . sccEq (eqBy hsModName) . hsModulesToGraph $ ms

