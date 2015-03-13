module PfeVersionCmd where
import PfeParse(noArgs)
import PFE0(pput)

import Now

pfeVersionCmd = [("version", (noArgs version,"display version number"))]

version = pput compileDate
