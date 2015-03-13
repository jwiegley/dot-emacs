module PfeTransformCmds where
import Pfe3Cmds(pp'')
import PfeParse(moduleArg)
import PFE_StdNames(getStdNames,prelValue,getPrelValue)
import RemovePatBinds
--import RemoveIrrefPats -- appers not to be reusable in extensions!
import SimpPatMatch(simpAllPatMatch,getSimpPatIds)
import SimpFunBind(simpAllFunBind)
import HsModuleMaps(mapDecls)

import PNT(PNT)
import TiNames(localVal)
--import StateM
import TiPNT()       -- to get instances for ValueId PNT

pfeTransformCmds =
    [("rmpatbind", (moduleArg rmpatbind,  "remove pattern bindings")),
--   ("rmirrpat",  (moduleArg rmirrpat,   "remove irrefutable patterns")),
--   ("onlynested",(moduleArg onlynested, "remove pattern bindings and irrefutable patterns")),
     ("patmatch",  (moduleArg patmatch,   "simplify pattern matches")),
     ("funbind",  (moduleArg funbind,   "simplify function bindings"))
    ]

rmpatbind m =
  do pErr <- getPrelValue "error"
     pp'' (mapDecls (remPatBinds' pErr bind_names)) id m

--rmirrpat    = pp'' (removeIrrefPats arg_names) id
--onlynested  = pp'' (remPatBinds' bind_names . removeIrrefPats arg_names) id


arg_names, bind_names :: [PNT]
arg_names   = [ localVal ("arg" ++ show n) | n <- [1..]] 
bind_names  = [ localVal ("bind" ++ show n) | n <- [1..]] 


patmatch m =
  do stdName <- getStdNames
     ids <- getSimpPatIds (prelValue stdName)
     pp'' (simpAllPatMatch ids.mapDecls simpAllFunBind) id m

funbind  = pp'' (mapDecls simpAllFunBind) id
