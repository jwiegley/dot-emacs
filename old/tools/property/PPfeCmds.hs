module PPfeCmds where

import TiPropDecorate(TiDecls) -- to choose result type from the type checker
--import PropSyntax(HsDeclI) -- to choose result type from the type checker

import SimpPatMatchProp()

--import Pfe3Cmds(pfe3Cmds)
import Pfe4Cmds(pfe4Cmds)
import PFE4(PFE4Info)
import Pfe3Metrics(pfe3MetricsCmds)
import PFEdeps(clean5)
import PfeHtmlCmds(pfeHtmlCmds)
import PfeDepCmds(pfeDepCmds)
import PfeCleanCmd(pfeCleanCmd)
import PfeVersionCmd(pfeVersionCmd)
import PfeChase(pfeChaseCmds)
import PfeTransformCmds(pfeTransformCmds)
import PfePropCmds(pfePropCmds)
import StrategoCmds(strategoCmds)
import IsabelleCmds(isabelleCmds)

--pfeCmds = pfe3Cmds++pfeChaseCmds++pfeHtmlCmds
ppfeCmds = pfe4Cmds tcOutput++pfe3MetricsCmds++pfeTransformCmds++pfeChaseCmds
	   ++pfeHtmlCmds++pfeDepCmds++pfePropCmds++strategoCmds++isabelleCmds
	   ++pfeCleanCmd clean5++pfeVersionCmd

tcOutput = id :: I (PFE4Info i2 (TiDecls i2))
--tcOutput = id :: I ([[HsModuleI i1 [HsDeclI i2]]],x,y)
type I a = a->a
