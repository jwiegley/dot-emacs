{-+
Chase source files through imports, assuming module names and file names agree.
-}
module PfeChase where
import Prelude hiding (putStrLn)
import Data.List(nub,partition,(\\))
import Control.Monad(unless,filterM)

import HsName(moduleName,ModuleName(..),isHierarchical)

--import Pfe0Cmds
import PFE0

import PfeParse
import AbstractIO
import PathUtils
import DirUtils(expand)
import PrettyPrint
import MUtils

pfeChaseCmds = [("chase",(fileArgs findMissing,"look for imported modules in given files/directories"))]

findMissing args =
  do checkProject
     fg <- getCurrentModuleGraph
     dirs <- filterM doesDirectoryExist args
     allfiles <- map normf # expand args
     let (ignored,newfiles) 
		 = partition (null.path2moduleName) (allfiles \\ map fst fg)
	 missing = nub [i|(_,(_,is))<-fg,i<-is] \\ map (fst.snd) fg
	 new = [(path,moduleName path (path2moduleName path))|path<-newfiles]

     unless (null ignored) $ pput $ "Ignoring:"<+>fsep ignored
     files <- map fst # chase dirs fg missing new
     --when (length files/=length (nub files)) $ pput "duplicates in file list"
     saveSrcList (nub files)
     projectStatus -- will report modules that are still missing
  where
    chase dirs fg missing new =
	case missing of
	  [] -> return fg
	  m:ms ->
	   do (fms,new') <- find m
	      case fms of
		[] -> chase dirs fg ms new' --didn't find m, skip & report later
		((f,_):fms) ->
		    do unless (null fms) $
		         pput $ "Using the first file for"<+>m<>":"<+>
			        fsep (f:map fst fms)
		       use f ms new'
      where
        find m =
          if isHierarchical m
	  then findHierarchical m
	  else return $ partition ((==m).snd) new

        findHierarchical m =
	     do let paths = [dir++[pathSep]++path|dir<-dirs,path<-moduleName2Paths m]
		fs <- filterM doesFileExist paths
		return ([(f,m)|f<-fs],new)

	use f ms new' =
	  do n@(m,is) <- moduleNode # preparseSourceFile f
	     let fg' = ((f,n):fg)
                 missing' = filter (isNew fg') is++ms
	     pput $ "Adding"<+>m<+>"from"<+>f
	     chase dirs fg' missing' new'

    isNew fg m = null . filter ((m==).fst.snd) $ fg

-- from a path like foo/bar/M.hs, extract M
path2moduleName =
    reverse . takeWhile (/=pathSep) . drop 1 . dropWhile (/='.') . reverse

moduleName2Paths m = 
  case m of
    MainModule path -> [path]
    PlainModule s -> [base++".lhs",base++".hs"]
      where
        base = map sep s
	sep '.' = pathSep
	sep c   = c
