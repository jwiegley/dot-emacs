module PFEdeps(
   PFE5MT,runPFE5,clean5,getSt5ext,updSt5ext,setSt5ext,
   --Dep,Deps,deps0,
   tdepModules,tdepModules',depModules,depModules',
   tdefinedNames,isDefaultDecl,isInstDecl,splitDecls

   , Deps2(..)                                          
   )
 where
import Prelude hiding (readFile,readIO)
import Data.Maybe(fromMaybe)
import Data.List(nub,sort)

import HsModule
import HsIdent(getHSName,HsIdentI(..))
import HasBaseStruct(basestruct,hsTypeSig,hsInfixDecl)
import HasBaseName(getBaseName)
import HsDeclStruct(DI(..))
import SrcLoc1(srcLoc)
import TypedIds(IdTy(..))

import QualNames(mkUnqual)
import PNT(PNT(..))
import UniqueNames(noSrcLoc)
--import TiNames(idTy)
--import TiModule() -- instance HasIdTy PNT -- grr!

import PFE0
import PFE2(getModuleTime)
import PFE3(parseModule)
import PFE4(PFE4MT,getSt4ext,updSt4ext,clean4,runPFE4,typeCheckModule)
import TiClasses(fromDefs)
import TiNames(instName,defaultName,derivedInstName)
import DefinedNames(definedNames,addName,classMethods,contextSize)
import TiDefinedNames(definedTypeName)
import FreeNames(freeNames) --freeValues
import PrettyPrint
import MUtils
import AbstractIO
import FileUtils
import DirUtils(optCreateDirectory,getModificationTimeMaybe,rmR)

type Dep n = [([n],([n],[Hash]))] -- tricky to use correctly, should be abstract!!
type Deps n = [(ModuleName,(ClockTime,Dep n))]
type Deps2 n = (Deps n,Deps n)

deps0 = [] :: Deps n

type PFE5MT n i1 i2 ds1 ds2 ext m = PFE4MT n i1 i2 ds1 ds2 (Deps2 i2,ext) m

runPFE5 ext = runPFE4 ((deps0,deps0),ext)

getSt5 :: Monad m => PFE5MT n i1 i2 ds1 ds2 ext m (Deps2 i2)
updSt5 :: Monad m => Upd (Deps2 i2)->PFE5MT n i1 i2 ds1 ds2 ext m ()
getSt5ext :: Monad m => PFE5MT n i1 i2 ds1 ds2 ext m ext
updSt5ext :: Monad m => Upd ext->PFE5MT n i1 i2 ds1 ds2 ext m ()

getSt5 = fst # getSt4ext
updSt5 = updSt4ext . apFst 
setSt5 = updSt5 . const

getSt5ext = snd # getSt4ext
updSt5ext = updSt4ext . apSnd
setSt5ext = updSt5ext . const

type Hash = Int

hash =
    checksum . quickrender . withPPEnv hashmode . ppi
  where
    checksum = foldr (\c h->3*h+fromEnum c) 0
    hashmode = defaultMode{layoutType=PPNoLayout,typeInfo=False}

-- Compute the dependency info for all modules in the project:
depModules = depModules' Nothing
tdepModules = tdepModules' Nothing

-- Update the dependeny info for a selected set of modules in the project:
depModules' optms =
    do (olddeps,oldtdeps) <- getSt5
       newdeps <- depModules'' olddeps syntaxDeps optms
       setSt5 (newdeps,oldtdeps)
       return newdeps
  where
    syntaxDeps = (depFile,untypedParse,True)
    untypedParse = fmap dup . parseModule'

tdepModules' optms =
    do (olddeps,oldtdeps) <- getSt5
       newtdeps <- depModules'' oldtdeps typedDeps optms
       setSt5 (olddeps,newtdeps)
       return newtdeps
  where
    typedDeps = (tdepFile,typedParse,False)
    typedParse m = (,) # parseModule' m <# typeCheckModule m
                   -- The module is parsed twice!

parseModule' = fmap snd . parseModule

depModules'' olddeps depsrc optms =
    do optCreateDirectory `projPath` depdir
       ms <- maybe allModules return optms
       updateDeps depsrc olddeps ms


updateDeps (depFile,parseMod,allInst) olddeps ms =
    do newdeps <- mapM upd ms
       let changed = map fst newdeps
           deps = newdeps++filter ((`notElem` changed).fst) olddeps
       return deps
  where
    
    upd m =
      do let olddep = lookup m olddeps
	 t <- getModuleTime m
	 if t `newerThan` (fst # olddep)
           then do dept <- maybeF getModificationTimeMaybe depf
		   if t `newerThan` dept then again else useOld dept
	   else return (m,fromJust' "PFEdeps.hs:124" olddep)

      where
        depf = depFile m
		   
        again =
          do epput $ "Extracting dependencies:"<+>m
             dep <- dependencies allInst # parseMod m
	     t <- updateDep depf dep
	     return (m,(t,dep))

        useOld dept =
           do dir <- fromJust' "PFEdeps.hs:120" # projectDir
	      let path = depf dir
		  ret dep = return (m,(fromJust' "PFEdeps.hs:123" dept,dep))
              --ret . read'' path =<< readFile path -- lazy
	      maybe again ret =<< maybeM (readIO =<< readFile path) -- strict

    updateDep depf dep =
      do optdir <- projectDir
         case optdir of
           Nothing -> getClockTime
	   Just dir ->
             do updated <- updateFile' (depf dir) (show dep)
	        getModificationTime (depf dir)

{-+
The hash is computed from the source AST, while the set of free names in
a declaration is computed from the type checked AST, to catch dependencies
on instances, which are made explicit by the dictionary translation.
Things like derived instances that do not appear in the source code
will be assigned hash value [].
-}
dependencies allInst (untyped,typed) = udeps++deps
  where
    deps0 = [(rdefs d,rfree d)|d<-fromDefs (hsModDecls typed)]
    udeps = [([],(fvs,[]))|([],fvs@(_:_))<-deps0]
    deps1 = mapSnd (nub.concat) $ collectByFst [(n,fvs)|(ns,fvs)<-deps0,n<-ns]
    deps  = [([n],(fvs,findHash n))|(n,fvs)<-deps1]
    findHash n = nub $ sort [h|(n',h)<-hs,n'==n]
    hs = [(n,h)|d<-fromDefs (hsModDecls untyped),let h=hash d,n<-rdefs d]

    mn = getBaseName (hsModName typed)
    rdefs = map getHSName . tdefinedNames allInst mn
    rfree = restrict . tfreeNames mn
    restrict = nub . concatMap (addowner.getHSName)
    --restrict = map getHSName

    addowner x = if o==x then [x] else [o,x]
      where o = owner x

    -- Map subordinate names to their owner (reduces the total number of names):
    owner x =
	case idty x of
	  ConstrOf t ty -> pnt t (Type ty)
	  FieldOf t ty -> pnt t (Type ty)
	  MethodOf c n ms -> pnt c (Class n ms)
	  _ -> x
      where
	pnt t idty = PNT (mkUnqual t) idty noSrcLoc
	idty (PNT _ ty _) = ty


-- To track dependencies on instances, include the names assigned to
-- instances by the type checker.
-- Also, to keep relevant type signatures and infix declarations, pretend that
-- they are part of the definitions of the identifiers the mention.
tdefinedNames allInst m d =
  case basestruct d of
    Just (HsInstDecl s optn ctx inst ds) -> if allInst then [] else [HsVar n]
      where n = fromMaybe (instName m s inst) optn
    Just (HsTypeSig s is c t) -> map HsVar is
    Just (HsInfixDecl s f is) -> is
    _ -> ns
  where ns = map fst (definedNames (addName d))

{-
Since the type checker lifts default methods out from the class declaration
to the top level, we make the class declaration depend on the default
methods, under the assumption that they will be included in slices if
the class is included...
-}
tfreeNames m d =
  case basestruct d of
    Just (HsDataDecl s c tp cs cls) ->
        [HsVar (derivedInstName m cl tn)|cl<-cls]++ns
      where tn = definedTypeName tp
    Just (HsClassDecl s c t fd ds) ->
         map fst (freeNames d)++map (fmap defaultName) methods
       where
         methods = map fst (classMethods undefined (contextSize c) ds)
    _ -> ns
  where ns = map fst (freeNames d)

isDefaultDecl d =
  case basestruct d of
    Just (HsDefaultDecl{}) -> True
    _ -> False

isInstDecl d =
  case basestruct d of
    Just (HsInstDecl{}) -> True
    _ -> False

{-+
To make it ease to include the right infix declarations and type signatures,
split them. For example, if * is needed but / is not, you can't keep or throw
away all of the infix declaration "infixl 7 *,/".
-}
splitDecls = concatMap splitDecl
splitDecl d =
  case basestruct d of
    Just (HsTypeSig s is c t) -> [hsTypeSig s [i] c t|i<-is]
    Just (HsInfixDecl s f is) -> [hsInfixDecl s f [i]|i<-is]
    _ -> [d]

--------------------------------------------------------------------------------
clean5 = withProjectDir clean
  where
    clean dir = do rmR [depdir dir]
		   clean4

--------------------------------------------------------------------------------

depdir dir=dir++"dep/"

depFile m dir = depdir dir++moduleInfoPath m++".g"
tdepFile m dir = depdir dir++moduleInfoPath m++".tg"
--------------------------------------------------------------------------------
