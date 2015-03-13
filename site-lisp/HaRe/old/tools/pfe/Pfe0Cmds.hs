-- Programatica Front-End Commands, level 0
module Pfe0Cmds where
import Prelude hiding (print,putStr,putStrLn,catch,readFile)
import Data.List((\\))
import Control.Monad(unless,when)
import Data.Maybe(fromJust)

import PFE0

import HsName(ModuleName(..),isMainModule,sameModuleName)
--import HsConstants(main_mod)
import HsLexerPass1(rmSpace,Pos(line)) -- for lines of code metrics

import PfeParse
import PrettyPrint
import MUtils
import SimpleGraphs(reverseGraph,reachable)
import DirUtils(optCreateDirectory)
import AbstractIO
import Statistics

pfe0 parseModule args = runPFE0Cmds () pfe0Cmds parseModule args

--runPFE0Cmds ext cmds = runPFE0 ext $ doCmd (cmds, projectStatus)
runPFE0Cmds ext cmds = runCmds (runPFE0 ext) cmds

pfe0Cmds = projman++graphqueries

addHelpCmd prg cmds0 = cmds where cmds=cmds0++helpCmd prg cmds

helpCmd prg cmds =
  [("help",(noArgs (putStrLn (usage prg cmds)),"list available commands"))]

projman =
  -- Project management (a project is a set of source files)
  [("new"     , (qfileArgs  new, "create a new project containing zero or more files")),
   ("add"     , (qfileArgs  add, "add files to the project")),
   ("remove"  , (qfileArgs  remove, "remove files from the project")),
   ("prune"   , (moduleArgs prune,"remove unreachable modules from the project")),
   ("files"   , (noArgs     files,"list files in the project")),
   ("options" , (noArgs     options,"show options in effect"))]

graphqueries =
  -- Module graph queries
  [("modules" , (moduleArgs modules,"show a topologically sorted list of modules")),
   ("graph"   , (graphArgs graph,"show module dependecy (sub)graph")),
--   ("dirgraph", (moduleArgs dirgraph,"show source directory dependecy (sub)graph")),
--   ("dotdirgraph", (moduleArgs dotdirgraph,"dot format source directory dependecy (sub)graph")),
   ("unused"  , (moduleArgs unused,"list unimported and unreachable modules")),
   ("file"    , (moduleArg  file,"which file is the module in")),
   ("module"  , (fileArg    module',"which module does the file contain")),
   ("loc"     , (moduleArgs locModules, "number of lines of code")),
   ("sizemetrics" , (noArgs sizeMetrics, "number of lines per module metrics")),
   ("locmetrics" , (noArgs locMetrics, "number of lines of code per module metrics")),
   ("importmetrics",(noArgs importMetrics, "number of imports per module metrics")),
   ("exportmetrics",(noArgs exportMetrics, "number of exports (importers) per module metrics"))]

--- Project management ---------------------------------------------------------
new    quiet args = do newProject; addPaths quiet args
add    quiet args = addPaths quiet args
remove quiet args = removePaths quiet args

files = putStr . unlines =<< allFiles

options = print =<< parserFlags

qfileArgs f = f #@ kwOption "-quiet" <@ filenames

--- Module graph queries -------------------------------------------------------
modules ms = do g <- getSortedSubGraph (just ms)
	        let sccs = map (map (fst.snd)) g
	        putStrLn "Topologically sorted strongly connected components:"
	        putStr (unlines (map (unwords.map pp) sccs))

graphArgs = moduleArgs' graphOpts
  where
    graphOpts = (,,) #@ kwOption "-rev" <@ kwOption "-dot" <@ kwOption "-dir"

graph (rev,dot,dir) =
    pput . out_conv_dirs @@ getSubGraph . just
  where
    out_conv_dirs  = if dir then out_conv . srcdirGraph  else out_conv . map snd
    out_conv = out . conv
    out   = if dot then dotFormat    else makeFormat
    conv  = if rev then reverseGraph else id

-- Dot format functions contributed by Claus Reinke:
     
dotFormat g =
   "digraph ModuleGraph {size=\"7.5,10.5\";ratio=fill;" $$
   vcat [q x<>"->"<>braces (fsep [q d<>";"|d<-xs])|(x,xs)<-g] $$
   "}"
  where
    q = doubleQuotes

makeFormat g = vcat [x<>":"<+>fsep xs|(x,xs)<-g]

--dirgraph    ms = pput . makeFormat =<< srcdirGraph ms
--dotdirgraph ms = pput . dotFormat =<< srcdirGraph ms

srcdirGraph g = dg
  where moddirs = [(m,dirname path)|(path,(m,_))<-g]
	moddir m = fromJust (lookup m moddirs)
	dg = mapSnd usort $
	     collectByFst
	       [(moddir m,dir')|(_,(m,ms))<-g,dir'<-usort (map moddir ms)]

dirname = current . reverse . dropWhile (/='/') . reverse
  where current "" = "./"
	current path = path
     
file m =
    do g <- getCurrentModuleGraph
       pput $ vcat [m<>":"<+>f|(f,(m',_))<-g,m'==m]

module' f =
    do g <- getCurrentModuleGraph
       pput $ vcat [f<>":"<+>m|(f',(m,_))<-g,f'==f]

getUnused ms =
  do fg <- getCurrentModuleGraph
     let g = map snd fg
         unimported = map fst g \\ [m|(m,_:_)<-reverseGraph g]
	 roots = if null ms then mains else ms
	   where mains = [m|(m,_)<-g,isMainModule m]
	 r = reachable g roots
	 unreached = map fst g \\ r
     when (null roots) $
       fail "No root modules given, no Main module in the project"
     return (fg,roots,unimported,unreached)

mainModules =
  do fg <- getCurrentModuleGraph
     return [m|(f,(m,_))<-fg,isMainModule m]

unused ms =
  do (_,roots,us,unr) <- getUnused ms
     if null us -- unlikely...
       then putStrLn "All modules are imported somewhere"
       else pput $ "The following modules are never imported:" $$
	           nest 4 (fsep us)
     unless (null unr) $
       do pput $
	    sep [ppi "The following modules are unreachable from",
		 nest 2 (fsep roots<>":")]
	  pput $ nest 4 (fsep unr)

prune ms =
  do (fg,_,_,unreached) <- getUnused ms
     removePaths False [f|(f,(m,_))<-fg,m `elem` unreached]

sizeMetrics =
    pput . ppStatistics "number of lines" "module"
      =<< mapM (forkM (fst.snd) (size #. readFile . fst))
      =<< getCurrentModuleGraph
  where
    size = length . lines

locMetrics =
    pput . ppStatistics "number of lines of code" "module"
      =<< mapM (forkM (fst.snd) (loc . snd #. lex0SourceFile.fst))
      =<< getCurrentModuleGraph

--forkM f g x = (,) (f x) # g x
forkM f g x =
  do y <- g x
      -- seq to process one file at a time in locMetrics & sizeMetrics
     seq y (return (f x,y))

loc = length . squeezeDups . map (line.fst.snd) . rmSpace

locModules = mapM_ locModule
locModule = locFile @@ findFile
locFile = pput . loc . snd @@ lex0SourceFile


importMetrics = graphMetrics id "number of imports"
exportMetrics = graphMetrics reverseGraph "number of importers"

graphMetrics f lbl =
    do g <- mapSnd length . f . map snd # getCurrentModuleGraph
       pput $ ppStatistics lbl "module" g
