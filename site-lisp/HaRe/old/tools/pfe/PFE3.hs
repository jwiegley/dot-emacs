{-+
PFE level 3: proper parsing of Haskell modules.
-}
module PFE3(module PFE3,XRefInfo) where

import ReAssocModule(reAssocModule)
import ScopeModule(scopeModule,XRefInfo,checkRefs)
import AST4ModSys(toMod)
import Modules(inscope)
import WorkModule(mkWM)
import Relations(emptyRel)
import PrettyPrint(pp,vcat,($$),(<>),(<+>))

import PFE0(Upd,moduleNode,findFile,lexAndPreparseSourceFile,getModuleInfixes,
            getModuleImports,updateModuleGraph,batchMode)
import PFE2--(getExports,getModuleExports)

import MUtils
import Control.Monad(when)

--------------------------------------------------------------------------------
type PFE3MT n i ds ext m = PFE2MT n i ds ext m

runPFE3 ext = runPFE2 ext
clean3 = clean2

--getSt3 :: Monad m => PFE3MT n i ds ext m (PFE3Info n)
--updSt3 :: Monad m => Upd (PFE3Info n)->PFE3MT n i ds ext m ()
getSt3ext :: Monad m => PFE3MT n i ds ext m ext
updSt3ext :: Monad m => Upd ext->PFE3MT n i ds ext m ()

--getSt3 = fst # getSt0ext
--updSt3 = updSt0ext . apFst 
--setSt3 = updSt3 . const

getSt3ext = getSt2ext
updSt3ext = updSt2ext
setSt3ext = updSt3ext . const
--------------------------------------------------------------------------------
--parseModule :: ... => ModuleName -> m (WorkModule ..,HsModule ...)
--parseSourceFile :: ... => FilePath -> m (WorkModule ..,HsModule ...)
parseModule       = parseSourceFile @@ findFile
parseSourceFile f = fst . snd # parseSourceFile' f

refsModule = refsSourceFile @@ findFile
refsSourceFile f = snd . snd # parseSourceFile'' f

parseModule' = parseSourceFile' @@ findFile

-- Parse, rewrite infix applications, check identifiers
parseScopeSourceFile = checkScope . snd @@ parseSourceFile'
  where
    checkScope (m,refs) = check (checkRefs refs) >> return m

    check [] = done
    check errs =
        fail $ pp $ "Scoping errors" $$ vcat [loc<>":"<+>err|(loc,err)<-errs]
    
-- Parse and rewrite infix applications according to their fixities
parseSourceFile' path =
    do infixes <- getModuleInfixes
       let re wm = reAssocModule wm infixes
       parseSourceFile''' re path

-- Parse *without* rewriting infixes
parseSourceFile'' = parseSourceFile''' (const id)

-- rewrite:  does the rewriting to fix the parse tree when the 
--           fixities of operators are known
-- filepath: the file to be parsed   

parseSourceFile''' rewrite filepath =
     do (ts,mod) <- lexAndPreparseSourceFile filepath
	let n@(m,imports) = moduleNode mod
	unlessM batchMode $
	  do oldimports <- getModuleImports m
	     when (imports/=oldimports) updateModuleGraph
	exp <- snd # getModuleExports m
	exports <- getExports (Just imports)
	let insc = inscope (toMod mod) (expOf exports)
	    wm = mkWM (insc,exp)
	    ex = mapSnd snd exports -- drop datestamp
	    (mod',refs) = scopeModule (wm,ex) (rewrite wm mod)
	return (ts,(((wm,ex),mod'),refs))
  where

{-+
To prevent pfebrower from crashing if the module graph is inconsistent,
expOf does not fail on references to unknown modules. Instead it returns
an empty export relation...
-}

    expOf exports m = maybe emptyRel snd (lookup m exports)

    {-
    -- For debugging:
    expOf exports m =
      case lookup m exports of
	Just (_,es) -> es
	_ -> error $ "PFE3: Didn't find export relation for: "++show m
    -}
