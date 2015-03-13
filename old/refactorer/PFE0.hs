-- Programatica Front-End, level 0, see README.html
module PFE0(
    PFE0MT,runPFE0,clean0,PFE0State, PFE0_IO, HasInfixDecls,
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
    moduleNode,newerThan,
    -- managing HaRe file history
    clearHistory, addToHistory, undoLatestInHistory,
    -- Hare editor interface
    getEditorCmds, State0, editorCmds, getSt0
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
import FileUtils hiding (readFileNow)
import AbstractIO
import NewSCC(scc)
import PPU
import CmdLineParser3
import ParserOptions
import ParseMonad(PM)

import Unlit(readHaskellFile)
import ParseMonad(parseTokens)
import HsLexerPass1(Lexer)
import HsLexMerge(mergeLex)

import EditorCommands
import qualified Control.OldException as CE (catch)
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
			    lexer :: Lexer,
			    parser :: PM (HsModuleI (SN ModuleName) i ds),
			    fixities :: ModuleFixities n,
			    srclist :: [FilePath],
			    tgraph :: Maybe (Maybe ClockTime,ModuleGraph),
			    sortedgraph :: Maybe SortedModuleGraph ,
                            editorCmds :: EditorCmds ,
			    history :: [(Bool,[(String,String)])] }

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
	   sortedgraph = Nothing,
           editorCmds = commandlineCmds ,
	   history = [] }

graph st = snd # tgraph st
-- Old:
--type PFE0Info n = (ModuleGraph,ModuleFixities n)
--pfe0info st = (graph st,fixities st)

getEditorCmds = editorCmds # getSt0

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
setSt0 = updSt0 . const

getSt0ext = snd # getSt
updSt0ext = updSt_ . apSnd
setSt0ext = updSt0ext . const

batchMode = batch # getSt0
setBatchMode b = updSt0 $ \st->st{batch=b}

{- the definition from Programatica.
runPFE0 ext pfeM lexerAndParser (opts,name,args0) =
  do let st0 = (initState0 name lexerAndParser){ppOpts=opts}
     withPFE0 (st0,ext) $ pfeM (name++" [options]") =<< initProject args0
-}

--------------------------------------------------------------------------
-- HaRe redefined runPFE0.  (was called runLoopPFE0).
runPFE0 ext pfeM lexerAndParser (opts,name,args0) = do 
  let st0 = (initState0 name lexerAndParser){ppOpts=opts}
  withPFE0 (st0,ext) $ editorLoop (name++" [options]") =<< initProject args0
  where
    editorLoop prg ("emacs":args) = do
      updSt0 $ \st->st{editorCmds=emacsCmds}
      loop prg args
    editorLoop prg ("vim":(vimPath:(vimServerName:args))) = do
      editorCmds <- mkVimCmds vimPath vimServerName
      updSt0 $ \st->st{editorCmds=editorCmds}
      loop prg args
    editorLoop prg args = do
      loop prg args

    loop prg args = do
      editorCmds <- editorCmds # getSt0
      let getCmd = lift (getEditorCmd editorCmds)
          sendMsg dialog msg = lift (sendEditorMsg editorCmds dialog msg)
          sendModified f = lift (sendEditorModified editorCmds f)
      l <- catchEnv getCmd (const $ return "stop")
      let cmdArgs@(cmd: ~(mod:_)) = words l
      sendMsg False $ "CMD:"++show cmdArgs
      unless (cmd=="stop") $ do
        if (cmd=="undo") then (undoLatestInHistory >> loop prg args) 
          else do when (cmd == "new") clearHistory                  
                  -- refactorings currently use exceptions freely:-(
                  -- AbstractIO defined catch as Prelude.catch, which doesn't
                  -- capture all exceptions; we need Control.Exception.catch..
                  -- we also need catch embedded in environment monad (catchEnv)
                  -- [now changed into state transformer..]
                  -- in the longer term, we need to avoid fatal exceptions within
                  -- refactorings, switching to Either or least to user exceptions!
                  -- NOTE: we need a placeholder for semantic information, to be
                  --       filled in and kept up-to-date by refactorings as they
                  --       find they need to parse&analyse files in the project;
                  --       that placeholder/semantic info will then have to be 
                  --       passed from one iteration to the next here
                  -- in the new programatica sources, "new"/"chase" don't seem to 
                  -- update the project state; as a workaround, we reinitialise
                  -- in each loop..
                  catchEnv (do initProject args0 
                               setBatchMode False
                               pfeM prg cmdArgs) 
                    (\e ->sendMsg True $ "CAUGHT EXCEPTION: " ++ show e)

                  loop prg args
    catchEnv m f = do s <- getSt
                      (r,s) <- lift (withStS s m `CE.catch` (withStS s . f))
                      setSt s
                      return r

------------------------------------------------------------------------
-- managing the refactoring history, which is of type 
-- [[(Filename,Filecontents)]], where both names and contents are Strings

clearHistory = updSt0 (\s->s{history=[]})

-- refactorer currently extends history whenever 
-- called upon, even if the editor file has been 
-- reset in the meantime!! need more communication
-- between editor and refactorer

addToHistory isSubRefactor files  = do sources <- mapM readFileNow files 
                                       updSt0 (\s->s{history=((isSubRefactor,(zip files sources)):(history s))})

undoLatestInHistory = do
  history <- history # getSt0
  editorCmds <- editorCmds # getSt0
  let sendModified f = lift (sendEditorModified editorCmds f)
      sendMsg dialog msg = lift (sendEditorMsg editorCmds dialog msg)
  case skipHistory ([],history) of
    (f@(file:files),rest) -> 
         do mapM_ (\(name,source)->writeFile name source >> sendModified name) f
            updSt0 (\s->s{history=rest})
    _ -> do sendMsg True "no refactorer undo history"

readFileNow name = do -- make sure file is read completely
                      contents <- readFile name 
                      seq (length contents) $ return contents

skipHistory (r, []) =(r,[])
{- flag: True means the back-up id for sub-refactoring. This function aims to help
   undoing composite refactorings
-}
skipHistory (r,h@((flag,files):rest)) 
       = if flag then skipHistory (((diffHistory r files)++ files),rest)  -- handle sub-refactoring
                 else (((diffHistory r files)++files), rest) 
  where 
    diffHistory::[(String,String)]->[(String,String)]->[(String,String)]
    diffHistory h1 h2 = filter (\(filename,content)->not (elem filename filenames)) h1
       where  filenames = map fst h2

 

------------------------------------------------------------------------

initProject args0 =
  do res <- try loadSrcList
     case res of
       Left err ->
         if isDoesNotExistError err
	 then blankProject args0
	 else ioError err
       Right files -> openProject projdir args0
  where
    projdir = defaultProjectDir

    loadSrcList =
      do paths <- lines # readFileNow (srclistPath projdir)
	 setSrcList paths
	 clearGraph
	 return paths

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

newProject =
  do let dir=defaultProjectDir
     optCreateDirectory dir
     updSt0 $ \st->st{cacheDir=Just dir}
     setSrcList []
     setpfe0info ((Nothing,[]),[])
     let opath = optionsPath dir
     writeFile opath . show =<< parserFlags
     updateModuleGraph

clearGraph = updSt0 $ \st->st{fixities=[],tgraph=Nothing,sortedgraph=Nothing}

saveSrcList paths =
  do setSrcList paths
     flip updateFile_ (unlines . set $ paths) `projPath` srclistPath

setSrcList paths = updSt0 $ \st->st{srclist=paths}

preparseModule = preparseSourceFile @@ findFile

preparseSourceFile path =
  do flags <- parserOpts # getSt0
     optAddPrelude fakeSN (prel flags) #
	(parseFile path =<< readHaskellFile (cpp flags) path)
  where
    parseFile path (litcmnts,code) = 
      do PFE0 {lexer=lexerPass0,parser=parseModule} <- getSt0
	 parseTokens parseModule path (lexerPass0 code)

-- lexAndPreparseSourceFile :: (HasEnv m PFE0Env, FileIO m) =>
--  => FilePath -> m ([(Token,(Pos,String))],HsModuleI i)
lexAndPreparseSourceFile path =
  do PFE0{parserOpts=flags,lexer=lexerPass0,parser=parseModule} <- getSt0
     lts@(_,ts) <- apSnd lexerPass0 # readHaskellFile (cpp flags) path
     m <- optAddPrelude fakeSN (prel flags) # parseTokens parseModule path ts
     return (mergeLex lts,m)

lex0SourceFile path =
  do PFE0{parserOpts=flags,lexer=lexerPass0} <- getSt0
     apSnd lexerPass0 # readHaskellFile (cpp flags) path

parserFlags = parserOpts # getSt0
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

getCurrentModuleGraph =
  do ifM (isJust . graph # getSt0) done quietUpdateModuleGraph
     fromJust . graph # getSt0

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

projectDir = cacheDir # getSt0
withProjectDir' n m = maybe n m =<< projectDir
withProjectDir = withProjectDir' done

allModules = moduleList # sortCurrentModuleGraph
allFiles = srclist # getSt0
getModuleInfixes = fixities # getSt0

moduleList g = [m|scc<-g,(_,(m,_))<-scc]

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

checkProject = withProjectDir' newProjectHelp return

newProjectHelp =
    do name <- myname # getSt0
       fail $ "Start by creating a new project using "++
	      name++" new or pfesetup"

addPaths = changePaths (++)
removePaths = changePaths (\\)

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
    conv '/'  = '-'
    conv '\\' = '_'
    conv ':'  = '_'
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
