module Pfe3Cmds where
import Prelude hiding (putStr,putStrLn)

import PfeParse(moduleArg)
import Pfe2Cmds(pfe2Cmds,runPFE2Cmds)
import PFE0(pput)
import PFE3(parseModule)
import WorkModule(inscpRel)

--import AbstractIO
import PrettyPrint
import MUtils((@@))

pfe3 ext = runPFE3Cmds ext pfe3Cmds
runPFE3Cmds ext = runPFE2Cmds ext

pfe3Cmds =
  pfe2Cmds ++
  [-- Analyzing the contents of modules
   ("inscope", (moduleArg inscope,"list entities in modules' top-level environment")),
   ("parse"  , (moduleArg (pp'' show id),"parse and show abstract syntax")),
   ("pp"     , (moduleArg pp_plain,      "parse and pretty-print modules"))
  ]

inscope m = showInscope . fst . fst =<< parseModule m
  where
    showInscope wm = pput $ sep [m<>":",nest 2 . ppi $ inscpRel wm]

pp_plain = pp' id
--ppscope = pp' withDebug

pp' = pp'' id

pp'' f ppOpts = (pput.ppOpts.ppi.f.snd) @@ parseModule

