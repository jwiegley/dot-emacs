module PFE4(
  PFE4MT,PFE4Info,runPFE4,clean4,
  getSt4ext,updSt4ext,setSt4ext,modEnv,
  typeCheckModule,rewriteAndTypeCheckModule,
  typeCheck,rewriteAndTypeCheck,topTypes,typeCheck',exTypeCheck,
  ) where
import Prelude hiding (putStrLn,readFile,catch,ioError)

--import Monad(when)
import Data.List(intersect)
import Data.Maybe(fromMaybe,isNothing)

import HsConstants(mod_Prelude,mod_Ix)
import HsModule(HsModuleI,ModuleName(..),hsModName)
import HsModuleMaps(mapDecls)
import TiModule(tcModuleGroup,representative,monomorphismRestriction)
import TiNames(topName)
import Relations(applyRel)
import WorkModule(Ent(..))
import TiPNT()
import TI(DeclsType,extendIEnv,extendEnv,concDeclsType,moduleContext,Typing(..),unzipTyped,run)
import TiError(Error)
import TiInstanceDB(Instance)

import PNT(PNT(..))
import HsIdent(HsIdentI(..))
import TypedIds(IdTy(Value),NameSpace(..),namespace)
import UniqueNames(noSrcLoc)
import HasBaseName(getBaseName)
import SourceNames(SN,fakeSN)
import ScopeModule(origName)

import PFE3(parseScopeSourceFile)
import PFE3(PFE3MT,runPFE3,getSt3ext,updSt3ext,clean3)
import PFE2(getExports)
import PFE0(Upd,epput,newerThan,optSubGraph,sortCurrentModuleGraph,projPath,projectDir,maybeF,withProjectDir,moduleInfoPath,allModules)
import PFE_Rewrites(getStdNames,prelValue,flRewrite)
import PFE_Rewrite
import PrettyPrint
import qualified Lift
import MUtils
import ExceptMT
--import StateMT(getSt,updSt_)
import SimpleGraphs(reachable)
import AbstractIO
import FileUtils(updateFile')
import DirUtils(optCreateDirectory,getModificationTimeMaybe,latestModTime,rmR)


type ModuleTypeInfo i ds =
    (ClockTime,([(RewriteName,HsModuleI (SN ModuleName) i ds)],
		([Instance i],DeclsType i)))

type PFE4Info i ds = [(ModuleName,ModuleTypeInfo i ds)]


modEnv :: PFE4Info i ds -> ModuleName -> Maybe (DeclsType i)
modEnv pfe4info m = snd . snd . snd # lookup m pfe4info

--id4 :: Upd (PFE4Info i ds)
--id4 = id

pfe4info0 = []::PFE4Info i ds

type PFE4MT n i1 i2 ds1 ds2 ext m = PFE3MT n i1 ds1 (PFE4Info i2 ds2,ext) m

-- Extra exeption monad transformer,
-- to be able to keep the structured type for type errors.
-- It's just only locally for now because of the extra lifting involved
type ExPFE4MT n i1 i2 ds1 ds2 ext m
  = WithExcept (Error (HsIdentI i2)) (PFE4MT n i1 i2 ds1 ds2 ext m)

runPFE4 ext = runPFE3 (pfe4info0,ext)

getSt4 :: Monad m => ExPFE4MT n i1 i2 ds1 ds2 ext m (PFE4Info i2 ds2)
updSt4 :: Monad m => Upd (PFE4Info i2 ds2)->ExPFE4MT n i1 i2 ds1 ds2 ext m ()
getSt4ext :: Monad m => PFE4MT n i1 i2 ds1 ds2 ext m ext
updSt4ext :: Monad m => Upd ext->PFE4MT n i1 i2 ds1 ds2 ext m ()

getSt4 = fst # lift getSt3ext
updSt4 = lift . updSt3ext . apFst 
setSt4 = updSt4 . const

getSt4ext = snd # getSt3ext
updSt4ext = updSt3ext . apSnd
setSt4ext = updSt4ext . const

expfe4 = id :: Upd (ExPFE4MT n i1 i2 ds1 ds2 ext m a) -- a type signature with holes
pfe4 = id :: Upd (PFE4MT n i1 i2 ds1 ds2 ext m a) -- a type signature with holes

typeCheckModule m = rewriteAndTypeCheckModule idRw m

rewriteAndTypeCheckModule rewrite@(Rewrite rwname0 _) m =
  do --epput $ "rewriteAndTypeCheckModule"<+>m
     r <- lookuprw.fst.snd.fromJust' "PFE4.hs:108b" .lookup m
            # rewriteAndTypeCheck rewrite (Just [m])
     --seq r $ epput $ "return from rewriteAndTypeCheckModule"<+>m
     return r
  where
    rwname = rwname0++"fl"
    lookuprw rws =
      fromJust' ("PFE4.hs:108a "++rwname++" "++show (map fst rws))
		(lookup rwname rws)

rewriteAndTypeCheck f = rewriteAndTypeCheck' f True
typeCheck             = typeCheck' True
topTypes              = typeCheck' False

exTypeCheck           = removeExcept . exRewriteAndTypeCheck' idRw True

{-
typeCheck' :: ... => Bool -> [ModuleName] -> t m (PFE4Info i2 ds)
-}
typeCheck' = rewriteAndTypeCheck' idRw

rewriteAndTypeCheck' rewrite wantAST optms =
  pfe4 $ 
  Lift.lift =<< removeExcept (exRewriteAndTypeCheck' rewrite wantAST optms)

exRewriteAndTypeCheck' userRewrite wantAST optms =
  do subsg <- flip optSubGraph optms # lift sortCurrentModuleGraph
     oldTypes <- getSt4
     stdNames <- lift getStdNames
     let rewrite = userRewrite `compRw` flRewrite
     types <- rewriteAndTypeCheck'' stdNames rewrite wantAST optms oldTypes subsg
     let newTypes = types++[old|old@(m,_)<-oldTypes,m `notElem` newms]
	 newms = map fst types
     setSt4 newTypes
     return types

rewriteAndTypeCheck'' stdNames (Rewrite rwname rwM) wantAST optms oldTypes subsg =
    expfe4 $
    do lift $ optCreateDirectory `projPath` typesdir
       rewrite <- lift rwM
       tcSccs rewrite [] [] subsg
  where
    subg = map snd (concat subsg)
    ms = fromMaybe (map fst subg) optms
    rms = map (fst.snd.head) subsg -- representative from each scc

    tcSccs rewrite types updated [] = return types
    tcSccs rewrite types updated (scc:sccs) =
	  do let sccms = map (fst.snd) scc
		 wanted = wantAST && (not.null $ sccms `intersect` ms)
             --lift $ epput $ "wantAST="<>wantAST<+>"wanted="<>wanted
	     (types',updated') <- tcScc rewrite wanted sccms types updated scc
	     tcSccs rewrite (types'++types) (updated'++updated) sccs

    tcScc rewrite wanted mns types updated scc@(_:_) =
        if wanted && any isNothing [lookup rwname.fst.snd=<<lookup m oldTypes|m<-mns]
           || not (null updated_imports)
	then tcAgain
	else useOld
      where
	updated_imports = imports_approx `intersect` updated

        -- A coarse approximation to what is needed by a module:
        -- (Advantage: this is the right thing for instances)
        imports_approx = reachable subg mns

	useOld =
	  do srct <- latestModTime srcfs
	     let opt_oldtypes = mapM (flip lookup oldTypes) mns
		 oldtt = minimum.map fst # opt_oldtypes
	     if srct `newerThan` oldtt
		then do tt <- lift $ maybeF getModificationTimeMaybe typesf
	                if srct `newerThan` tt
			  then tcAgain
			  else do --lift $ epput $ "Using old types:"<+>fsep mns
                                  types' <- readTypeFiles
				  let t = fromJust' "PFE4.hs:177" tt
				  -- !!! Type info is duplicated here:
				  return ([(m,(t,([],types')))|m<-mns],[])
		else return (zip mns (fromJust' "PFE4.hs:180" opt_oldtypes),[])

        parseSCM = mapM ((mapDecls rewrite . snd # ) .
                         parseScopeSourceFile .fst)

	tcAgain =
	  do ms <- lift (parseSCM scc)
             lift $ epput $ "Type checking:"<+>fsep mns
             tms:>:types' <- tcScc' ms
	     optdir <- lift projectDir
	     (updated,t) <-
               case optdir of
		 Nothing ->
	           do --No access to the old types here, so we have to assume
	              --they have changed!! (This should be easy to improve.)
                      t <- getClockTime
		      return (True,t)
		 Just dir ->
		   do updated <- updateTypeFiles dir types'
		      t <- getModificationTime (typesf dir)
		      return (updated,t)
	     --lift $ epput $ [(getBaseName (hsModName tm),(show t,([(rwname,"()")],"()")))|tm<-tms]
	     -- !!! Type info is duplicated here:
	     return ([(getBaseName (hsModName tm),(t,([(rwname,tm)],types')))|tm<-tms],
		     if updated then mns else [])


        tcScc' ms =
           do mono <- (/=Just "no") # maybeM (getEnv "PFE_monomorphism")
	      --Lift.lift $
              either raise return . run $
                 tcScc'' mono ms

	tcScc'' mono ms@(_:_) =
	    monomorphismRestriction mono $
	    extendIEnv (concat insts) $ extendEnv (concDeclsType envs) $
	    moduleContext mns $ tcModuleGroup stdNames rewrite ms
	  where
	    (insts,envs) = unzip [mt|(m,(_,(_,mt)))<-types,
				     m `elem` imports_approx,m `elem` rms]

	srcfs = map fst scc
	mn = representative mns -- pick one representative from the scc
	kindsf = kindsFile mn
	typesf = typesFile mn
	instsf = instsFile mn

        updateTypeFiles dir (insts,(kinds,types)) =
	  do uk <- updateFile' (kindsf dir) (showTypings kinds)
	     ut <- updateFile' (typesf dir) (showTypings types)
             ui <- updateFile' (instsf dir) (show insts)
	     return (uk||ut||ui)

        readTypeFiles =
	  do dir <- fromJust' "PFE4.hs:233" # lift projectDir
             kinds <- readTypings # readFile (kindsf dir)
	     types <- readTypings # readFile (typesf dir)
	     insts <- let path = instsf dir
                      in read'' path # readFile path
	     return (insts,(kinds,types))

showTypings xys = shl (length xs).shls (map (fmap pn) xs) . shls ys $ ""
  where
     shls xs r = foldr shl r xs
     shl x = shows x.showChar '\n'
     xs:>:ys = unzipTyped xys
     pn (PNT n _ _) = n -- hmm

readTypings s = rdls (lines s)
  where
     rdls (n:ls) = uncurry zipTypings (splitAt (rd n) ls)
     zipTypings [] _ = []
     zipTypings (x:xs) ~(y:ys) = (fmap pnt (rd x):>:rd y):zipTypings xs ys
     pnt n = PNT n Value noSrcLoc -- hmm!
     rd s = read'' "PFE4.readTypings" s

--------------------------------------------------------------------------------
clean4 = withProjectDir clean
  where
    clean dir = do rmR [typesdir dir]
		   clean3

--------------------------------------------------------------------------------

typesdir dir=dir++"types/"

typesFile m dir = typesdir dir++moduleInfoPath m++".types"
kindsFile m dir = typesdir dir++moduleInfoPath m++".kinds"
instsFile m dir = typesdir dir++moduleInfoPath m++".insts"

--------------------------------------------------------------------------------
instance CatchIO err m => CatchIO err (WithExcept e m) where
  m `catch` f = do r <- lift $ try $ removeExcept m
	           case r of
                     Left ioe -> f ioe
		     Right ok -> either raise return ok
  ioError = lift . ioError
