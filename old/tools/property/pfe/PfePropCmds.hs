module PfePropCmds where
import Prelude hiding (writeFile,print,readFile,readIO)
import Monad(when)
import List(sort,isPrefixOf)
import Maybe(fromJust,mapMaybe)
import Sets

import PFE0(pput,allModules,preparseModule,findFile,moduleInfoPath,getSubGraph)
import PFE3(parseModule) --parseSourceFile,
--import PFE2(analyzeModules',pfe2info0)
import PfeParse(moduleArgs,moduleArg,qualId,parseQualId) --,just
import PFE_Certs(assertions) --certDir,certsDir,certModuleDir,certDatestampPath
import PfeDepCmds(depgraph,tdepgraph,ppOrig,depGraph)

import PrettyPrint
import AbstractIO
import DirUtils(optCreateDirectory)
--import FileUtils(updateFile)
import MUtils
import PfeParse

import HsModule
import HsModulePretty
import HsModuleMaps(seqEntSpec,mapDecls,mapModMN)
import HsIdent(getHSName)
import ToQC(moduleToQC)
import HasBaseName(getBaseName)
import NameMaps(mapNames)
import PFEdeps(tdepModules',tdefinedNames,isDefaultDecl,isInstDecl,splitDecls)
import SimpleGraphs(reachable)
--import DefinedNames(definedNames)
import TiNames(topName)
import TiClasses(filterDefs)
import TypedIds(IdTy(Assertion))

pfePropCmds =
  [--("certscan",(moduleArgs certscan,"update certificate templates for assertions")),
   ("assertions",(moduleArgs assertionNames,"list names of named assertion")),
   ("asig",      (sequentArg asig,"write an assertion signature to stdout")),
   ("tasig",     (sequentArg tasig,"write an assertion signature to stdout")),
   ("adiff",     (diffArg adiff,"compare an assertion signature to a file")),
   ("tadiff",    (diffArg tadiff,"compare an assertion signature to a file")),
   ("qc",        (moduleArg toQC,"translate to QuickCheck")),
   ("slice",     (qualId slice,"extract a slice (needed part) of the program")),
   ("pqc",       (qualId prunedToQC,"pruned translation to QuickCheck")),
   ("qcslice",   (qualId qcslice,"translate a slice to QuickCheck"))]

diffArg f = args ("<path> "++sequentSyntax) (f @@ parseDiffArg)
parseDiffArg [] = fail "Was expecting a path and a sequent"
parseDiffArg (path:sequent) = (,) path # parseSequent sequent

sequentArg f = args sequentSyntax (f @@ parseSequent)
sequentSyntax = "<M.A> [ .. | <M1.A1 ... Mn.An> ]"

parseSequent [] = fail "At least a conclusion is required"
parseSequent (conc:hyps) = (,) # parseQualId conc <# parseHyps hyps
  where
    parseHyps [".."] = return Nothing -- everything
    parseHyps args = Just # mapM parseQualId args

asig = print @@ assertionSignature
tasig = print @@ tassertionSignature

assertionSignature = assertionSignature' depgraph
tassertionSignature = assertionSignature' tdepgraph

assertionSignature' depgr (qid,_) =
  do (deps,(g,ids,used)) <- depgr [qid]
     return $ sort [(n,h)|n<-used,(m,(t,ds))<-deps,(dns,(_,h))<-ds,n `elem` dns]

adiff (path,sequent) =
  do old <- readIO =<< readFile path
     new <- assertionSignature sequent
     signatureDiff old new

tadiff (path,sequent) =
  do old <- readIO =<< readFile path
     new <- tassertionSignature sequent
     signatureDiff old new

signatureDiff [] [] = return ()
signatureDiff ns [] = pput $ "No longer depends on:"<+>ppOrigs (map fst ns)
signatureDiff [] ns = pput $ "New dependencies:"<+>ppOrigs (map fst ns)
signatureDiff allold@((n1,h1):old) allnew@((n2,h2):new) =
  case compare n1 n2 of
    LT -> do pput $ "No longer depends on:"<+>n1
             signatureDiff old allnew
    GT -> do pput $ "New dependency:"<+>ppOrig n2
             signatureDiff allold new
    EQ -> do when (h1/=h2) $ pput $ "Changes have been made to:"<+>ppOrig n1
				  -- <+>parens (h1<>"/="<>h2) -- debug
	     signatureDiff old new

ppOrigs = ppiFSeq . map ppOrig

assertionNames optms =
  do ms <- if null optms then allModules else return optms
     mapM_ assertions1 ms
  where
    assertions1 m =
      mapM_ (pput. (m<+>)) =<< (map fst . assertions # preparseModule m)

toQC = pputModuleToQC @@ parseModule

--bnParseModule m = apSnd baseNames # parseModule m 

pputModuleToQC = pput . bnModuleToQC
bnModuleToQC = moduleToQC . apSnd baseNames

baseNames = mapModMN getBaseName . mapNames getBaseName

prunedToQC q@(m,n) =
  do (t,deps) <- fromJust . lookup m # tdepModules' (Just [m])
     let g = depGraph [(d,fs)|(ds,(fs,hash))<-deps,d<-ds]
	 needed = reachable g [topName Nothing m n Assertion]
	 isNeeded = any (`elem` needed) . map getHSName . tdefinedNames True m
         keepNeeded = mapDecls (filterDefs isNeeded)
     pputModuleToQC . apSnd keepNeeded =<< parseModule m

slice = tslice' snd
qcslice = slice' bnModuleToQC

slice' = slice'' True depgraph
tslice' = slice'' False tdepgraph

slice'' allInst depgraph trans q@(m,n) =
  do ms <- map (fst.snd) # getSubGraph (Just [m])
     (_,(_,_,used)) <- depgraph [q]
     let needed = mkSet used
     optCreateDirectory "slice"
     mapM_ (writeModuleSlice allInst trans needed) ms

writeModuleSlice allInst trans needed m =
  unlessM (isPrefixOf "hi/libs/" # findFile m) $ -- skip Prelude & std libs
  do let path = "slice/"++moduleInfoPath m++".hs" -- !!!
     pput (m<+>"in"<+>path)
     writeFile path.pp.
       trans.apSnd (sliceModule needed isNeeded.mapDecls splitDecls)
        =<< parseModule m
  where
    isNeeded d = isDefaultDecl d || allInst && isInstDecl d || isNeeded' d
    isNeeded' = any (`elementOf` needed) . map getHSName . tdefinedNames allInst m

sliceModule needed isNeeded (HsModule s m es is ds) =
    HsModule s m (fmap sliceExports es) (sliceImports is) (sliceDecls ds)
  where
    sliceDecls = filterDefs isNeeded
    sliceExports = mapMaybe sliceExport
    sliceImports = map sliceImport

    sliceImport (HsImportDecl s m q as optspecs) =
      HsImportDecl s m q as $ fmap (apSnd sliceEnts) optspecs

    sliceExport e =
      case e of
        ModuleE m -> Just e
	EntE ent -> EntE # sliceEnt ent

    sliceEnts = mapMaybe sliceEnt
    sliceEnt e =
      case e of
	ListSubs i is -> ListSubs # keep i <# return is
	_ -> seqEntSpec (fmap keep e)

    keep n = if n `elementOf` needed
	     then Just n
	     else Nothing


{-
certscan ms =
  do info <- analyzeModules' pfe2info0 (just ms)
     optCreateDirectory certsDir
     mapM_ (updateModuleAssertions info) =<< getCurrentModuleGraph
  where
    updateModuleAssertions info (src,(m,_)) =
      do srct <- getModificationTime src
	 let stampfile = certDatestampPath m
         optct <- getModificationTimeMaybe stampfile
	 when (srct `newerThan` optct) $
            do optCreateDirectory (certModuleDir m)
               scan
	       writeFile stampfile ""
      where
        scan =
          mapM_ updAssertionCert.assertions.snd =<<parseSourceFile info src

        updAssertionCert (n,pa) =
           do let dir=certDir m (pp n)
              optCreateDirectory dir
	      unchanged <- updateFile (dir++"/assert.txt") (pp pa)
	      unless unchanged $ epput $ "Updated:"<+>m<>"."<>n
-}
