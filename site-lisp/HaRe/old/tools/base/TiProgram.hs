module TiProgram(tcProgramFiles,tcProgram,tcModules,tcModuleGroup) where
import ParseProgram
import ScopeProgram
import HsModule(hsModName)

import TiModule(tcModuleGroup)
import TI(extendIEnv,extendEnv,(+++),errmap,Typing(..))

import WorkModule(analyzeModules)

import PrettyPrint
import MUtils
import Lift

--- Parse and type check a program, given as a list of file names.
-- tcProgramFiles
--   :: ... => [FilePath] -> IO ([[HsModule ds']],DeclsType)
tcProgramFiles parseMod = lift . tcModules @@ parseProgram parseMod

--- Rewrite and type check a program, given as a list of parsed modules
-- tcProgram
--   :: ... => [HsModule ds] -> IO ([[HsModule ds']],DeclsType)
tcProgram mods = tcModules @@ lift . analyzeModules $ mods

tcModules prg = tcModules'.fst =<< scopeProgram prg

-- Type check dependency analyzed modules:
tcModules' modss = tcSccs ([],[]) [] modss
  where
    tcSccs tmods tsccs sccs =
      case sccs of
        [] -> return (reverse tsccs,tmods)
        scc:sccs' -> do (tscc,tmods1,insts) <- tcScc scc
		        extendIEnv insts $
			  extendEnv tmods1 $
			  tcSccs (tmods1+++tmods) (tscc:tsccs) sccs'

    tcScc ms@(_:_) =
        do tms:>:(insts,mt) <- errmap (ctx++) $ tcModuleGroup ms
	   return (tms,mt,insts)
      where
        mns = map hsModName ms
        ctx = pp ("In module(s) "<+>fsep mns)++":\n"
