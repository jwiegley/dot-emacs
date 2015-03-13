module ASTCmds where
import Prelude hiding (print)

import Pfe0Cmds(moduleArg)
--import PFE2(analyzeModules',pfe2info0)
import PFE3(parseModule)
import HsModule(hsModDecls)

import AbstractIO
import MUtils((@@))
--import Front2AST
import Front2Stratego
import StrategoPretty()
--import Phugs

astCmds = [--("trans"   , moduleArg trans),
           --("phugs"   , moduleArg eval),
           ("prove"   , (moduleArg stratego,"translate to Stratego"))]
{-
trans ms =
    do info <- analyzeModules' pfe2info0 (Just ms)
       mapM_ (trans1 info) ms
  where
    trans1 info m = print.trM.snd=<<parseModule info m


trM = map trD . hsModDecls
-}
---------------------------------------------------

stratego = (print.transM.snd) @@ parseModule

transM = transDecs . hsModDecls

---------------------------------------------------
{-
eval ms =
    do info <- analyzeModules' pfe2info0 (Just ms)
       mapM_ (trans1 info) ms
  where
    trans1 info m = print.phugs.translateM.snd=<<parseModule info m


translateM = map translateD . hsModDecls
-}
