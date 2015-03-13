module Pfe2Cmds where
--import Prelude hiding (putStr,putStrLn)

--import WorkModule(analyzeSCM,expRel,inscpRel,mkWM)
import Relations(applyRel)
import SourceNames(SN(..))
import SrcLoc1(loc0)

import Pfe1Cmds(pfe1Cmds)
import PfeParse(moduleArg,idArgs,runCmds)
import PFE2(runPFE2,getModuleExports,getAllExports)
import PFE0(pput,allModules)

--import AbstractIO
import PrettyPrint
import MUtils(done)

pfe2 ext = runPFE2Cmds ext pfe2Cmds

runPFE2Cmds ext = runCmds (runPFE2 ext)

pfe2Cmds =
    pfe1Cmds ++
    [-- Module system queries (import/export, top level environment)
  -- ("topenv"  , (Null      topenv, "check all import and export specifications")), -- just update, no output
     ("exports" , (moduleArg exports,"list entities exported by the modules")),
     ("find"    , (idArgs    find,"find exported entities with the given names"))
    ]

--- Module system queries (import/export, top level environment) ---------------
exports = showModuleInfo snd

showModuleInfo sel m = pput . ppModuleInfo sel m =<< getModuleExports m

ppExports = ppModuleInfo snd
ppModuleInfo sel m info = sep [m<>":",nest 2 . ppi $ sel info]

find ids = do exports <- getAllExports
	      mapM_ (mapM_ pp1 . find1 exports) ids
 where
   pp1 (m,ents) = pput (m<>":"<+>vcat ents)

   find1 mes id = 
     [(m,ents)|(m,(t,es))<-mes,
	       let ents=applyRel es (sn id),
	       not (null ents)]

--topenv = analyzeModules >> done

sn n = SN n loc0 -- !!
