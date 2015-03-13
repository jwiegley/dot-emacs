-- Programatica Front-End, level 0, see README.html
module PFE0(
    PFE0MT,runPFE0,clean0,
    pput,epput,
    Upd,getSt0ext,updSt0ext,setSt0ext, -- for extending the state
    ModuleNode,ModuleGraph,
    getCurrentModuleGraph,sortCurrentModuleGraph,getSortedSubGraph,getSubGraph,
    allModules,allFiles,moduleList,
    findFile,findFile',findNode,findNode',
    getModuleInfixes,getModuleImports,
    updateModuleGraph,
    parserFlags,ppFlags,
    batchMode,setBatchMode,
    newProject,addPaths,removePaths,saveSrcList,checkProject,projectStatus,
    lex0SourceFile,preparseModule,preparseSourceFile,lexAndPreparseSourceFile,
    projectDir,projPath,maybeF,withProjectDir,withProjectDir',newProjectHelp,
    moduleInfoPath,
    -- Pure functions:
    optSubGraph,subGraph,
    -- Independent of PFE:
    moduleNode,newerThan
  ) where
import Prelude hiding (readFile,writeFile,putStr,putStrLn,catch,ioError)
import Data.List(sort,nub,(\\))
import Control.Monad(when,unless)
import Data.Maybe(fromMaybe,fromJust,isJust)

import HsModule
import HsAssocStruct
import HsIdent
import ReAssoc(HasInfixDecls,getInfixes)
import NamesEntities(getQualified)
import QualNames(QualNames) 
import SourceNames(SN,fakeSN)
import HasBaseName(getBaseName)

import MUtils(( # ),(@@),done,collectByFst,mapFst,apFst,apSnd,ifM,seqMaybe)
import SimpleGraphs(reverseGraph,reachable)
--import EnvMT
import MT (MT(..))
import StateMT(WithState,withSt,withStS,getSt,setSt,updSt,updSt_)
import DirUtils
import FileUtils
import AbstractIO
import NewSCC(scc)
import PPU
import ParserOptions
import ParseMonad(PM)

import Unlit(readHaskellFile)
import ParseMonad(parseTokens)
import HsLexerPass1(Lexer)
import HsLexMerge(mergeLex)

--------------------------------------------------------------------------------
-- Types manipulated at PFE level 0:

type ModuleNode = (FilePath,(ModuleName,[ModuleName]))
type ModuleGraph = [ModuleNode]
type SortedModuleGraph = [ModuleGraph] -- strongly connected components

type Fixities n = [(HsIdentI n,HsFixity)]
type ModuleFixities n = [(ModuleName,Fixities n)]

--------------------------------------------------------------------------------

--type PFE i ds m a = WithEnv (Parser i ds m) m a
--type Parser i ds m = FilePath -> m (HsModuleI i ds)

--pfe :: (PFE_IO m, DefinedNames (SN HsName) ds, HasInfixDecls (SN HsName) ds)
--    => (Maybe String->Parser (SN HsName) ds m) -> [String] -> m ()

--type PFE0Env i ds = ((Flags,(Bool,PPHsMode)),(Lexer,PM (HsModuleI i ds)))

data State0 n i ds = PFE0 { myname :: String,
			    batch :: Bool,
			    cacheDir :: Maybe FilePath,
			    parserOpts :: ParserOptions.Flags,
			    ppOpts :: (Bool,PPHsMode),
			    lexer :: Bool->Lexer,
			    parser :: PM (HsModuleI (SN ModuleName) i ds),
			    fixities :: ModuleFixities n,
			    srclist :: [FilePath],
			    tgraph :: Maybe (Maybe ClockTime,ModuleGraph),
			    sortedgraph :: Maybe SortedModuleGraph }

initState0 name (lexer,parser)
  = PFE0 { myname = name, -- name of command, for usage message
	   batch = True, -- batch mode (always trust data in internal caches)
	   cacheDir = Nothing, -- location of current project cache
	   parserOpts = flags0,
	   ppOpts = ppOpts0,
	   lexer = lexer,
	   parser = parser,
	   fixities = [],
	   srclist = [],
	   tgraph = Nothing,
	   sortedgraph = Nothing }

graph st = snd # tgraph st
-- Old:
--type PFE0Info n = (ModuleGraph,ModuleFixities n)
--pfe0info st = (graph st,fixities st)


-- Leave room for extending the state (poor man's subtyping):
type PFE0State n i ds nextlevel = (State0 n i ds,nextlevel)

type PFE0MT n i ds ext m = WithState (PFE0State n i ds ext) m
withPFE0 :: Monad m => PFE0State n i ds ext -> PFE0MT n i ds ext m a -> m a
withPFE0 = withSt 

{-+
All level 0 functions work in arbitrary monads that provide access to
the level 0 state (and some other things). The following type
signatures *restricts* level 0 functions to the PFE0MT monad transformer.
We don't need the extra generality at the moment and the restriction
should make the inferred types more readable (but since
GHC doesn't do any context reduction, they are still not very
readable...)
-}
type Upd s = s->s
getSt0 :: Monad m => PFE0MT n i ds ext m (State0 n i ds)
updSt0 :: Monad m => Upd (State0 n i ds)->PFE0MT n i ds ext m ()
getSt0ext :: Monad m => PFE0MT n i ds ext m ext
updSt0ext :: Monad m => Upd ext->PFE0MT n i ds ext m ()

getSt0 = fst # getSt
updSt0 = updSt_ . apFst
setSt0 x = updSt0 (const x)

getSt0ext = snd # getSt
updSt0ext = updSt_ . apSnd
setSt0ext x = updSt0ext (const x)

batchMode :: Monad m => PFE0MT n i ds ext m Bool
batchMode = batch # getSt0
setBatchMode b = updSt0 $ \st->st{batch=b}

getLexer () = do PFE0{lexer=l,parserOpts=flags} <- getSt0
	         return (l (plogic flags))
              
runPFE0 ext pfeM lexerAndParser (opts,name,args0) =
  do let st0 = (initState0 name lexerAndParser){ppOpts=opts}
     withPFE0 (st0,ext) $ pfeM (name++" [options]") =<< initProject args0

initProject args0 =
  do res <- try (loadSrcList ())
     case res of
       Left err ->
         if isDoesNotExistError err
	 then blankProject args0
	 else ioError err
       Right files -> openProject projdir args0
  where
    projdir = defaultProjectDir

    loadSrcList () =
      do paths <- lines # readFile (srclistPath projdir)
	 setSrcList paths
	 clearGraph ()
	 return paths

    clearGraph () =
      updSt0 $ \st->st{fixities=[],tgraph=Nothing,sortedgraph=Nothing}

blankProject args0 =
  do flags0 <- parserFlags
     let (flags,args) = parserOptions flags0 args0
     updSt0 $ \st->st{parserOpts=flags}
     return args

openProject dir args0 =
  do updSt0 $ \st->st{cacheDir=Just dir}
     flags0 <- parserFlags
     let opath = optionsPath dir
     flags1 <- fromMaybe flags0 # (readFileMaybe opath)
     let (flags,args) = parserOptions flags1 args0
     updSt0 $ \st->st{parserOpts=flags}
     --quietUpdateModuleGraph
     when (flags/=flags1) $ writeFile opath (show flags)
     return args

setpfe0info (tg,fs) =
     updSt0 $ \st->st{tgraph=Just tg,fixities=fs,sortedgraph=Nothing}

newProject ::
  (PFE0_IO err m,IOErr err,HasInfixDecls i ds,QualNames i m1 n, Read n,Show n)=>
  PFE0MT n i ds ext m ()
newProject =
  do let dir=defaultProjectDir
     optCreateDirectory dir
     updSt0 $ \st->st{cacheDir=Just dir}
     setSrcList []
     setpfe0info ((Nothing,[]),[])
     let opath = optionsPath dir
     writeFile opath . show =<< parserFlags
     updateModuleGraph

saveSrcList paths =
  do setSrcList paths
     flip updateFile_ (unlines . set $ paths) `projPath` srclistPath

setSrcList paths = updSt0 $ \st->st{srclist=paths}

preparseModule m = preparseSourceFile =<< findFile m

preparseSourceFile path =
  do flags <- parserFlags
     optAddPrelude fakeSN (prel flags) #
	(parseFile path =<< readHaskellFile (cpp flags) path)
  where
    parseFile path (litcmnts,code) = 
      do parseModule <- parser # getSt0
	 lexerPass0 <- getLexer()
	 parseTokens parseModule path (lexerPass0 code)

-- lexAndPreparseSourceFile :: (HasEnv m PFE0Env, FileIO m) =>
--  => FilePath -> m ([(Token,(Pos,String))],HsModuleI i)
lexAndPreparseSourceFile path =
  do PFE0{parserOpts=flags,parser=parseModule} <- getSt0
     lexerPass0 <- getLexer()
     lts@(_,ts) <- apSnd lexerPass0 # readHaskellFile (cpp flags) path
     m <- optAddPrelude fakeSN (prel flags) # parseTokens parseModule path ts
     return (mergeLex lts,m)

lex0SourceFile path =
  do PFE0{parserOpts=flags} <- getSt0
     lexerPass0 <- getLexer()
     apSnd lexerPass0 # readHaskellFile (cpp flags) path

parserFlags :: (Functor m,Monad m) => PFE0MT n i ds ext m (ParserOptions.Flags)
parserFlags = parserOpts # getSt0

ppFlags :: (Functor m,Monad m) => PFE0MT n i ds ext m (Bool,PPHsMode)
ppFlags = ppOpts # getSt0

-- Pretty print with options from PFE environment and put on stdout:
pput x =
  do o <- ppFlags
     putStrLn$ ppu o $ x

-- Pretty print with options from PFE environment and put on stderr:
epput x =
  do o <- ppFlags
     ePutStrLn$ ppu o $ x

findFile m = fst # findNode m
findNode m = findNode' m =<< getCurrentModuleGraph


findFile' :: (Functor m, Monad m) => ModuleName -> ModuleGraph -> m FilePath
findFile' m g = fst # findNode' m g

findNode' :: Monad m => ModuleName -> ModuleGraph -> m ModuleNode
findNode' m g =
    case  [n|n@(_,(m',_))<-g,m'==m] of
      [n] -> return n
      []  -> fail $ pp $ "Unknown module:"<+>m
      _   -> fail $ pp $ "Module defined in several files:"<+>m

getModuleImports m = snd . snd # findNode m

getCurrentModuleGraph ::
  (PFE0_IO err m,IOErr err,HasInfixDecls i ds,QualNames i m1 n, Read n,Show n)
   => PFE0MT n i ds ext m ModuleGraph
getCurrentModuleGraph =
  do ifM (isJust . graph # getSt0) done quietUpdateModuleGraph
     fromJust . graph # getSt0

sortCurrentModuleGraph ::
  (PFE0_IO err m,IOErr err,HasInfixDecls i ds,QualNames i m1 n, Read n,Show n)
   => PFE0MT n i ds ext m [ModuleGraph]
sortCurrentModuleGraph =
  do optsg <- sortedgraph # getSt0
     case optsg of
       Just sg -> return sg
       _ -> do g <- getCurrentModuleGraph
	       case checkGraph g of
	         Just errs -> fail $ pp $ moduleGraphReport errs
	         _ -> do let sg = sortGraph g
			 updSt0 $ \st->st{sortedgraph=Just sg}
			 return sg

getSubGraph optms = concat # getSortedSubGraph optms
getSortedSubGraph optms = flip optSubGraph optms # sortCurrentModuleGraph

projectDir :: (Functor m,Monad m) => PFE0MT n i ds ext m (Maybe FilePath)
projectDir = cacheDir # getSt0
withProjectDir' n m = maybe n m =<< projectDir
withProjectDir x = withProjectDir' done x

allModules ::
  (PFE0_IO err m,IOErr err,HasInfixDecls i ds,QualNames i m1 n, Read n,Show n)
   => PFE0MT n i ds ext m [ModuleName]
allModules = moduleList # sortCurrentModuleGraph

allFiles :: (Functor m,Monad m) => PFE0MT n i ds ext m [FilePath]
allFiles = srclist # getSt0

getModuleInfixes :: (Functor m,Monad m) => PFE0MT n i ds ext m (ModuleFixities n)
getModuleInfixes = fixities # getSt0

moduleList g = [m|scc<-g,(_,(m,_))<-scc]

projectStatus ::
  (PFE0_IO err m,IOErr err,HasInfixDecls i ds,QualNames i m1 n, Read n,Show n)=>
  PFE0MT n i ds ext m ()
projectStatus =
  do checkProject
     files <- allFiles
     if null files
       then do putStrLn "You have a new, empty project."
	       putStrLn "Add files to it by using: pfe add <files>"
       else do let n = length files
	       putStrLn $ "The project contains "++
			       if n==1
			       then "one source file."
			       else show (length files)++" source files."
	       putStrLn "(To list the files, use: pfe files)"
	       updateModuleGraph -- skip?

checkProject :: (Functor m,Monad m) => PFE0MT n i ds ext m FilePath
checkProject = withProjectDir' newProjectHelp return

newProjectHelp :: (Functor m,Monad m) => PFE0MT n i ds ext m a
newProjectHelp =
    do name <- myname # getSt0
       fail $ "Start by creating a new project using "++
	      name++" new or pfesetup"

addPaths q = changePaths (++) q
removePaths q = changePaths (\\) q

changePaths op quiet paths =
  do checkProject
     old <- allFiles
     new <- expand paths
     let files = old `op` paths
     saveSrcList files
     --optUpdateModuleGraph
     updateModuleGraph' quiet

sortGraph :: ModuleGraph -> [ModuleGraph]
sortGraph g = map (map post) . scc . map snd $ g
  where
    mfs = [(n,f)|(f,(n,_))<-g]
    post (n,is) = (fromMaybe (error "PFE0.sortGraph") $ lookup n mfs,(n,is))


checkGraph g =
    if null dups && null missing
    then Nothing
    else Just (dups,missing)
  where
    dups = filter duplicated mfs
      where duplicated (m,fs) = length fs/=1
    mfs = collectByFst [(m,f)|(f,(m,_))<-g]
    known = set (map fst mfs)
    missing = collectByFst [(i,m)|(_,(m,is))<-g,i<-is,i `notElem` known]


moduleGraphReport (mfs,missing) = reportDuplicates $$ reportMissing
  where
    reportDuplicates = sep (map reportDuplicate mfs)

    reportMissing = if null missing
		    then empty
		    else sep [ppi "Source files missing for (add files with 'pfe add' or 'pfe chase'): ",
			      nest 4 (vcat (map needed missing))]
        where needed (i,ms) = i<>","<+>"needed by"<+>fsep ms

    reportDuplicate (m,fs) = m<+>"defined in more than one file:"<+>fsep fs

optUpdateModuleGraph,quietUpdateModuleGraph,updateModuleGraph ::
  (PFE0_IO err m,IOErr err,HasInfixDecls i ds,QualNames i m1 n, Read n,Show n)=>
  PFE0MT n i ds ext m ()
optUpdateModuleGraph = ifM (isJust . graph # getSt0) updateModuleGraph done

quietUpdateModuleGraph = updateModuleGraph' True
updateModuleGraph      = updateModuleGraph' False 

-- Another type signature to improve the readablility of inferred types:
updateModuleGraph' ::
  (PFE0_IO err m,IOErr err,HasInfixDecls i ds,QualNames i m1 n, Read n,Show n)=>
  Bool -> PFE0MT n i ds ext m ()

updateModuleGraph' quiet =
    do files <- allFiles
       tg <- optLoadModuleGraph files
       ofix <- getModuleInfixes
       (g,fixities) <- unzip # mapM (updateModuleImports ofix tg) files
       -- The graph written to modgraphPath must be current, since source files
       -- are reread only if they are newer than modgraphPath!
       flip writeFile (show g) `projPath` modgraphPath
       t <- maybe getClockTime return =<<
              getModificationTime' `projPath` modgraphPath
       updateGraphTextFiles g
       let r = maybe [] (pp . moduleGraphReport) (checkGraph g)
       unless (quiet || null r) $ ePutStrLn r
       --saveSrcList files
       setpfe0info ((Just t,g),fixities)
  where

    optLoadModuleGraph files =
        maybe (loadModuleGraph files) return . tgraph =<< getSt0

    loadModuleGraph files =
      do optgpath <- fmap modgraphPath # projectDir
	 case optgpath of
	   Just gpath ->
	     do g <- (readM =<< readFile gpath) `catch` const (return [])
	        t <- if null g
		     then return Nothing
		     else Just # getModificationTime' gpath
	        return (t,g::ModuleGraph)
	   _ -> return (Nothing,[])

    updateModuleImports ofix (gt,g) modulePath =
        case lookup modulePath g of
	  Nothing -> getModuleImports modulePath
	  Just mi ->
	    ifM ((`newerThan` gt) # getModificationTime' modulePath)
	        (getModuleImports modulePath)
	        (useOldImports ofix modulePath mi)

    getModuleImports modulePath =
        do m <- preparseSourceFile modulePath
	   m_infixes <- updateInfixes m
	   let node = moduleNode m
	   return ((modulePath,node),m_infixes)

    useOldImports oldfixities modulePath mi@(mn,_) =
      do infixes <- case lookup mn oldfixities of
	              Just infixes -> return infixes
	              _ -> withProjectDir' no yes
		       where yes dir = readM=<<readFile (infixFile dir mn)
			     no = fail$"Missing fixity info for: "++show mn
	 return ((modulePath,mi),(mn,infixes))

    --updateInfixes :: (Printable i,HasInfixDecls i ds,HasIO m) => HsModuleI i ds -> m Bool
    updateInfixes m =
	do let infixes = mapFst getQualified (getInfixes (hsModDecls m))
	       mn = getBaseName (hsModName m)
	       upd dir = do optCreateDirectory (infixdir dir)
			    updateFile_ (infixFile dir mn) (show infixes)
           withProjectDir upd
	   return (mn,infixes)

    updateGraphTextFiles fg = withProjectDir upd
      where
        upd dir = do updateFile_ (dir++"ModuleSourceFiles.txt") (txt2 fg)
	             updateFile_ (dir++"ModuleGraphRev.txt") (txtn rg)
        g = map snd fg
	rg = reverseGraph g
        txtn = unlines . map (\(m,is)->pp m++" "++unwords (map pp is))
        txt2 = unlines . map (\(f,(m,_))->pp m++" "++f)

moduleNode m = (getBaseName (hsModName m),{-set$-} map getBaseName (hsModImportsFrom m))
--------------------------------------------------------------------------------

t `newerThan` Nothing = True
t `newerThan` Just t' = t>t'

set xs = sort (nub xs)

optSubGraph g = maybe g (subGraph g)

subGraph g ms = [scc|scc<-g,any (`elem` r) [m|(_,(m,_))<-scc]]
  where r = reachable (map snd (concat g)) ms

updateFile_ path str = updateFile path str >> done

maybeF m f = maybe (return Nothing) (m.f) =<< projectDir

m `projPath` f = do d <- fmap f # projectDir
		    seqMaybe (fmap m d)

--------------------------------------------------------------------------------

clean0 :: SystemIO m =>  PFE0MT n i ds ext m ()
clean0 = withProjectDir clean
  where
    clean dir =
      rmR [modgraphPath dir,
	   dir++"ModuleSourceFiles.txt",
	   dir++"ModuleGraphRev.txt",
	   infixdir dir]
      >>done

--------------------------------------------------------------------------------

defaultProjectDir = "hi/"
infixdir dir=dir++"infix/"
srclistPath dir= dir++"srclist.txt"
modgraphPath dir= dir++"FileModules.hv"
optionsPath dir= dir++"options"

infixFile dir m = infixdir dir++moduleInfoPath m++".hv"

moduleInfoPath m = map conv (pp (m::ModuleName))
  where
    conv '/' = '-'
    conv c = c

--------------------------------------------------------------------------------
{-
instance CatchIO err m => CatchIO err (WithEnv e m) where
  m `catch` f = do e <- getEnv
                   lift (withEnv e m `catch` (withEnv e . f))
  ioError = lift . ioError
-}
instance CatchIO err m => CatchIO err (WithState s m) where
  m `catch` f = do s0 <- getSt
                   (a,s1) <- lift $ withStS s0 m `catch` (withStS s0 . f)
		   setSt s1
		   return a
  ioError = lift . ioError

-- a class synonym:
class (FileIO m,DirectoryIO m,CatchIO e m,StdIO m,SystemIO m,TimeIO m) => PFE0_IO e m | m->e
instance (FileIO m,DirectoryIO m,CatchIO e m,StdIO m,SystemIO m, TimeIO m) => PFE0_IO e m
