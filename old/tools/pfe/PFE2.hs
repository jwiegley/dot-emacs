-- Programatica Front-End, level 2, see README.html
module PFE2(
  PFE2MT,runPFE2,clean2,
  getSt2ext,updSt2ext,setSt2ext,
  getAllExports,getExports,getModuleExports,getModuleExportsTime,getModuleTime
  ) where
import Prelude hiding (readFile,putStrLn)
import Data.Maybe(isJust,isNothing,fromJust)
import Data.List(nub,intersect,(\\))

import HsModule
import WorkModule(analyzeSCM,expRel,ExpRel,readRel,showRel)
import Relations(Rel)
--import Ents(Ent)
import PFE0

import PrettyPrint(pp,fsep,(<+>))
import MUtils
import StateMT(getSt,updSt_)
import AbstractIO
import FileUtils
import DirUtils(optCreateDirectory,getModificationTimeMaybe,rmR)

type Exports n = [(ModuleName,(ClockTime,ExpRel n))]

type PFE2Info n = Exports n
pfe2info0 = []::PFE2Info n

type PFE2MT n i ds ext m =  PFE0MT n i ds (PFE2Info n,ext) m

runPFE2 ext = runPFE0 (pfe2info0,ext)

getSt2 :: Monad m => PFE2MT n i ds ext m (PFE2Info n)
updSt2 :: Monad m => Upd (PFE2Info n)->PFE2MT n i ds ext m ()
getSt2ext :: Monad m => PFE2MT n i ds ext m ext
updSt2ext :: Monad m => Upd ext->PFE2MT n i ds ext m ()

getSt2 = fst # getSt0ext
updSt2 = updSt0ext . apFst 
setSt2 = updSt2 . const

getSt2ext = snd # getSt0ext
updSt2ext = updSt0ext . apSnd
setSt2ext = updSt2ext . const

-- The latest time at which the module or one of its imports was modified:
getModuleTime m =
    do (path,(_,imports)) <- findNode m
       srct <- getModificationTime path
       expts <- mapM getModuleExportsTime imports
       return (maximum (srct:expts))

getModuleExportsTime m = fst # getModuleExports m     

getModuleExports m =
    maybe (fail $ pp $ "Unknown module:"<+>m) return . lookup m
      =<< getExports (Just [m])

getAllExports = getExports Nothing

getExports optms =
  do oldExports <- getSt2
     ms <- maybe allModules return optms
     b <- batchMode
     if b && haveAll oldExports ms
       then return oldExports
       else do exports <- analyzeModules' oldExports optms
               setSt2 exports
               return exports
  where
    haveAll old ms = null (nub ms\\map fst old)

-- Compute the WorkModules for all modules in the project:
--analyzeModules = analyzeModules' pfe2info0 Nothing

-- Compute the WorkModules for a selected set of modules in the project:
analyzeModules' oldExports optms =
    do optCreateDirectory `projPath` scopedir
       g <- sortCurrentModuleGraph
       exports <- scopeScms [] [] (optSubGraph g optms)
       let newms = map fst exports
           oldexports = [oe|oe@(m,_)<-oldExports,m `notElem` newms]
       return (exports++oldexports)
  where

    scopeScms exports updated [] = return exports
    scopeScms exports updated (scm:scms) =
      do (exports',updated') <- scopeScm exports updated scm
	 scopeScms (exports'++exports) (updated'++updated) scms

    scopeScm exports updated scm =
      do es <- mapM getOldExport scm
	 let imps = imports scm
	     updimps = imps `intersect` updated -- updated imports
         case mapM id es of
	   Just exports' | null updimps ->
	        do let ms = map (fst.snd) scm
		   return (zip ms exports',[])
	   _ -> do epput $ "Analyzing:" <+>fsep (map fst scm)
		   a <- analyzeSCM (mapSnd snd exports) # preparseSCM scm
		   case a of
		     Left err -> fail (pp err)
		     Right wms' ->
		       do (unchanged,ts) <- unzip # mapM updateWorkModule wms'
			  let updated' = [m|((m,_),False)<-zip wms' unchanged]
			      exports' = zipWith f ts wms' 
			      f t (m,wm) = (m,(t,expRel wm))
			  return (exports',updated')

    imports scm = nub [i|(f,(m,is))<-scm,i<-is]
    preparseSCM = mapM (preparseSourceFile.fst)

    getOldExport (f,(m,_)) =
      do let opt_oexp = lookup m oldExports
	     oexpt = fmap fst opt_oexp
         -- Is the export relation in the internal cache present and fresh?
	 b <- batchMode
	 srct <- if b then return undefined else getModificationTime f
	 if if b then isNothing oexpt else srct `newerThan` oexpt
	   then do optdir <- projectDir
		   case optdir of
		     Nothing -> return Nothing -- no external cache
		     Just dir ->
		       do let expf = exportsFile dir m
			  expt <- getModificationTimeMaybe expf
			  srct <- if b
				  then getModificationTime f
				  else return srct
			  --Ditto for the export relation in the external cache?
			  if srct `newerThan` expt
			    then return Nothing
			    else maybeM (((,) (fromJust expt) . readRel)
                                          # readFileNow expf)
	   else return opt_oexp
    --fromJust' = fromMaybe (error "PFE2.getOldExport")

    --getInscope (_,(m,_)) = read # readFile (inscopeFile m)

    updateWorkModule (m,wm) =
      do optdir <- projectDir 
         case optdir of
           Nothing ->
	     do --No access to the old exports here, so we have to assume
	        --they have changed!! (This should be easy to improve.)
                t <- getClockTime
		return (True,t)
	   Just dir ->
             do --updateFile (inscopeFile dir m) (show (inscpRel wm))
                let expf = exportsFile dir m
		updated <- updateFile' expf (showRel (expRel wm))
		t <- getModificationTime expf
		return (updated,t)
--------------------------------------------------------------------------------
clean2 = withProjectDir clean
  where
    clean dir = do rmR [scopedir dir]
		   clean0

--------------------------------------------------------------------------------

scopedir dir=dir++"scope/"

exportsFile dir m = scopedir dir++moduleInfoPath m++".exports"
--inscopeFile dir (Module s) = scopedir dir++s++".inscope"

--------------------------------------------------------------------------------
