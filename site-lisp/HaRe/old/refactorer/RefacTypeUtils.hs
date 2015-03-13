
----------------------------------------------------------------------------------------------------------------
-- Module      : RefacTypeUtils

-- Maintainer  : refactor-fp\@kent.ac.uk  
-- |
--
-- This module contains a collection of program analysis and transformation functions (the API) that work
-- over the Type Decorated AST. Most of the functions defined in the module are taken directly from the API,
-- but in some cases are modified to work with the type decorated AST.
--
-- In particular some new functions have been added to make type decorated AST traversals easier.
--
-- In HaRe, in order to preserve the
-- comments and layout of refactored programs, a refactoring modifies not only the AST but also the token stream, and
-- the program source after the refactoring is extracted from the token stream rather than the AST, for the comments
-- and layout information is kept in the token steam instead of the AST. As a consequence, a program transformation
-- function from this API modifies both the AST and the token stream (unless explicitly stated). So when you build 
-- your own program transformations, try to use the API to do the transformation, as this can liberate you from 
-- caring about the token stream.
--
-- As the API is based on Programatica's abstract syntax for Haskell, we have re-exported those related module from
-- Programatica, so that you can browse the datatypes for the abstract syntax. Alternatively, you can go to 
-- Programatica's webpage at: <http://www.cse.ogi.edu/~hallgren/Programatica/>. For Strafunski, you can find it 
-- at: <http://www.cs.vu.nl/Strafunski/>.
--  
-- This type decorated API is still in development. Any suggestions and comments are very much welcome.


------------------------------------------------------------------------------------------------------------------

module RefacTypeUtils(module DriftStructUtils, module StrategyLib, module RefacTITypeSyn, module PosSyntax,
                  module SourceNames, module UniqueNames, module PNT, 
                  module Ents, module Relations, module QualNames, module TypedIds 
 -- * Program Analysis 
    -- ** Imports and exports
   ,inScopeInfo, isInScopeAndUnqualified, hsQualifier, {-This function should be removed-} rmPrelude 
   ,exportInfo, isExported, isExplicitlyExported, modIsExported

    -- ** Variable analysis
    ,hsPNs,hsPNTs,hsDataConstrs,hsTypeConstrsAndClasses, hsTypeVbls
    ,hsClassMembers, HsDecls(hsDecls,isDeclaredIn, replaceDecls)
    ,hsFreeAndDeclaredPNs,hsFreeAndDeclaredNames
    ,hsVisiblePNs, hsVisibleNames
    ,hsFDsFromInside, hsFDNamesFromInside 

    -- ** Property checking
    ,isVarId,isConId,isOperator,isTopLevelPN,isLocalPN,isTopLevelPNT
    ,isQualifiedPN,isFunPNT, isFunName, isPatName, isFunOrPatName,isTypeCon,isTypeSig,isFunBind,isPatBind,isSimplePatBind
    ,isComplexPatBind,isFunOrPatBind,isClassDecl,isInstDecl,isDirectRecursiveDef
    ,usedWithoutQual,canBeQualified, hasFreeVars,isUsedInRhs
    ,findPNT,findPN      -- Try to remove this.
    ,findPNs, findEntity
    ,sameOccurrence   
    ,defines,definesTypeSig, isTypeSigOf
    ,HasModName(hasModName), HasNameSpace(hasNameSpace)  
   
    
    -- ** Modules and files
    ,clientModsAndFiles,serverModsAndFiles,isAnExistingMod
    ,fileNameToModName, strToModName, modNameToStr

    -- ** Locations
    ,defineLoc, useLoc,locToPNT,locToPN,locToExp, getStartEndLoc  

 -- * Program transformation 
    -- ** Adding
    ,addDecl ,addItemsToImport, addHiding, rmItemsFromImport, addItemsToExport
    ,addParamsToDecls, addGuardsToRhs, addImportDecl, duplicateDecl, moveDecl
    -- ** Rmoving
    ,rmDecl, rmTypeSig, commentOutTypeSig, rmParams
    ,rmItemsFromExport, rmSubEntsFromExport, Delete(delete)
    -- ** Updating
    ,Update(update)
    ,qualifyPName,rmQualifier,renamePN,replaceNameInPN,autoRenameLocalVar

-- * Miscellous
    -- ** Parsing, writing and showing
   ,parseSourceFile,writeRefactoredFiles, showEntities ,showPNwithLoc, newProj, addFile, chase
    -- ** Locations
   ,toRelativeLocs, rmLocs
    -- ** Default values
   ,defaultPN,defaultPNT,defaultModName,defaultExp,defaultPat, defaultExpUnTyped
  
    -- ** Identifiers, expressions, patterns and declarations
    ,pNTtoPN,pNTtoName,pNtoName,nameToPNT, nameToPN,pNtoPNT
    ,expToPNT, expToPN, nameToExp,pNtoExp,patToPNT, patToPN, nameToPat,pNtoPat
    ,definingDecls, definedPNs
    ,simplifyDecl
    -- ** Others
   ,mkNewName, applyRefac, applyRefacToClientMods
                   
    -- The following functions are not in the the API yet.
    ,getDeclToks, causeNameClashInExports, inRegion , ghead, glast, gfromJust, unmodified, prettyprint,
    getDeclAndToks

-- * Typed AST traversals (added by CMB)
    -- * Miscellous
    ,removeFromInts, getDataName, checkTypes, getPNs, getPN, getPNPats, mapASTOverTAST
 )
where
import Prelude hiding (putStr,putStrLn,writeFile,readFile)
import Data.Maybe
import Data.List hiding (delete)
import Data.Char
--------------------------------
import PfeChase
import PFE0 
import PFE2
import PFE3(parseModule,parseModule', parseSourceFile')
import PFE4
import PosSyntax hiding (ModuleName, HsName, SN)
import SourceNames 

import ScopeModule
import UniqueNames hiding (srcLoc)
import HsName
import HsLexerPass1
import AbstractIO 
import PNT 
import TiPNT
import SimpleGraphs(reverseGraph,reachable)
import Ents hiding (isValue)
import Relations
import QualNames
import TypedIds hiding (NameSpace, HasNameSpace)
import WorkModule
import TiDecorate
import TI hiding (TI)

import Pfe4Cmds

import PrettyPrint
import Unlit(readHaskellFile,writeHaskellFile)
import MUtils hiding (swap)
import EditorCommands(sendEditorModified)
import qualified MT(lift)
import HsTokens
-------------------------
import RefacTITypeSyn
import RefacTypeLocUtils
-------------------------
import StrategyLib hiding (findFile)

#if __GLASGOW_HASKELL__ <604 

instance (Monoid a, Monoid b) => Monoid (a,b) where
   mappend (a,b) (a',b') = (mappend a a', mappend b b')
   mempty                = (mempty, mempty)
#endif


------------------------------------------------------------------------------------------

{- | The Delete class. -}
class (Term t, Term t1)=>Delete t t1 where
   
  -- | Delete the occurrence of a syntax phrase in a given context.
  delete::(MonadPlus m, MonadState (([PosToken],Bool),t2) m)=> t   -- ^ The syntax phrase to delete.
                                                          ->t1     -- ^ The contex where the syntax phrase occurs.
                                                          ->m t1   -- ^ The result.

-- An expression can only be deleted in certain circumstances.
instance (Term t) => Delete HsExpP t where
  delete e t 
    = applyTP (once_tdTP (failTP `adhocTP` inExp)`choiceTP` failure) t   
     where
     {-  inExp ((Exp (HsApp e1 e2))::HsExpP)
        |  sameOccurrence e e1 
        = do deleteFromToks e1
             return e2 -}
       inExp (TiDecorate.Exp (HsApp e1 e2)::HsExpP)
        | sameOccurrence e e2 
        = do deleteFromToks e2 getStartEndLoc
             return e1
       inExp (TiDecorate.Exp (HsList es))
         |isJust $ find (\x->sameOccurrence e x) es
        = do ((toks,_),others)<-get 
             let toks'=deleteEnt toks $ getStartEndLoc toks e
             put ((toks',modified),others)
             return (TiDecorate.Exp (HsList (es \\[e])))
       inExp _ = mzero
  
       sameOccurrence t1 t2
        = rmParen t1== rmParen t2 && srcLocs t1 == srcLocs t2    

       rmParen (TiDecorate.Exp (HsParen e)) = rmParen e
       rmParen e = e        

       failure = error "Delete: This expression can not be deleted!"
instance (Term t) => Delete HsPatP t where
   
  delete p t
    = applyTP (once_tdTP (failTP `adhocTP` inPats)) t
    where
      inPats (ps::[HsPatP])
        |isJust $ find(\x->sameOccurrence p x) ps
        = do deleteFromToks p  getStartEndLoc
             return (ps\\[p])
      inPats _ = mzero

instance (Term t) => Delete HsImportDeclP t where
  delete imp t 
   = applyTP (once_tdTP (failTP `adhocTP` inImps)) t
   where 
     inImps (imps::[HsImportDeclP])
       | isJust $ find (\x->sameOccurrence imp x) imps
       = do deleteFromToks imp startEndLocIncFowNewLn
            return (imps \\ [imp])
     inImps _ = mzero


{- | The Update class, -}
class (Term t, Term t1)=>Update t t1 where

  -- | Update the occurrence of one syntax phrase in a given scope by another syntax phrase of the same type.
  update::(MonadPlus m, MonadState (([PosToken],Bool),(Int,Int)) m)=>  t     -- ^ The syntax phrase to be updated.
                                                             -> t     -- ^ The new syntax phrase.
                                                             -> t1    -- ^ The contex where the old syntex phrase occurs.
                                                             -> m t1  -- ^ The result.
 
instance (Term t) =>Update HsExpP t where

 update oldExp newExp  t
   = applyTP (once_tdTP (failTP `adhocTP` inExp)) t
   where 
    inExp (e::HsExpP)
     | e == oldExp && srcLocs e == srcLocs oldExp 
       = do (newExp', _) <-updateToks oldExp newExp prettyprint
            return newExp'
    inExp e = mzero

instance (Term t) =>Update PNT t where
  update oldExp newExp  t
   = applyTP (once_tdTP (failTP `adhocTP` inExp)) t
   where 
    inExp (e::PNT)
     | e == oldExp && srcLocs e == srcLocs oldExp 
       = do (newExp',_) <- updateToks oldExp newExp prettyprint
            return newExp'
    inExp e = mzero

instance (Term t) =>Update HsMatchP t where
  update oldExp newExp  t
   = applyTP (once_tdTP (failTP `adhocTP` inExp)) t
   where 
    inExp (e::HsMatchP)
     | e == oldExp && srcLocs e == srcLocs oldExp 
       = do (newExp',_) <- updateToks oldExp newExp prettyprint
            return newExp'
    inExp e = mzero
    
instance (Term t) =>Update HsPatP t where

 update oldPat newPat  t
   = applyTP (once_tdTP (failTP `adhocTP` inPat)) t
   where 
    inPat (p::HsPatP)
     | p == oldPat && srcLocs p == srcLocs oldPat 
       = do (newPat', _) <- updateToks [oldPat] [newPat] (prettyprintPatList False)
            return $ ghead "update" newPat'
    inPat e = mzero

instance (Term t) =>Update [HsPatP] t where

 update oldPat newPat  t
   = applyTP (once_tdTP (failTP `adhocTP` inPat)) t
   where 
    inPat (p::[HsPatP])
     | sameOccurrence p oldPat 
       = do  (newPat', _) <- updateToks oldPat newPat (prettyprintPatList False)
             return newPat'
    inPat e = mzero

instance (Term t) =>Update HsDeclsP t where

 update oldDecl@(Decs x y) newDecl@(Decs x2 y2)  t
   = applyTP (once_tdTP (failTP `adhocTP` inDecl)) t
   where 
    inDecl (d::HsDeclsP)
     | sameOccurrence d oldDecl 
       = do
            (newDecl', _) <- updateToks oldDecl newDecl prettyprint
            return newDecl'
    inDecl e = mzero

instance (Term t) =>Update [HsDeclP] t where

 update oldDecl newDecl  t
   = applyTP (once_tdTP (failTP `adhocTP` inDecl)) t
   where 
    inDecl (d::[HsDeclP])
     | sameOccurrence d oldDecl 
       = do
            (newDecl',_) <- updateToks oldDecl newDecl prettyprint
            return newDecl'
    inDecl e = mzero 

instance (Term t) =>Update HsDeclP t where

 update oldDecl newDecl  t
   = applyTP (once_tdTP (failTP `adhocTP` inDecl)) t
   where 
    inDecl (d::HsDeclP)
     | sameOccurrence d oldDecl
       = do (newDecl',_) <- updateToks oldDecl newDecl prettyprint
            return newDecl'
    inDecl e = mzero

instance (Term t) =>Update HsImportDeclP t where

 update oldImpDecl newImpDecl  t
   = applyTP (once_tdTP (failTP `adhocTP` inDecl)) t
   where 
    inDecl (d::HsImportDeclP)
     | sameOccurrence d oldImpDecl 
       =do (newImpDecl', _) <-updateToks oldImpDecl newImpDecl prettyprint
           return newImpDecl'
    inDecl e = mzero

instance (Term t) => Update HsExportEntP t where
   update oldEnt@(EntE s) newEnt@(EntE s1) t
     = applyTP (once_tdTP (failTP `adhocTP` inEnt)) t
       where
         inEnt (e::HsExportEntP)
           | sameOccurrence e oldEnt
          =  do (s1',_) <- updateToks s s1 prettyprint
                return (EntE s1')
         inEnt e = mzero

instance (Term t) => Update HsTypeP t where
 update oldType newType t
   = applyTP (once_tdTP (failTP `adhocTP` inType)) t 
   where
     inType (t::HsTypeP)
        | sameOccurrence t oldType
       = do (newType', _) <- updateToks oldType newType prettyprint
            return newType'
     inType t = mzero

{- 

{- | The Swap Class. The instances may be not complete, tell us what you need so that we can add it.-}
class (Term t, Term t1 ) => Swap t t1 where

  -- | Swap the occurrences of two syntax phrases( of the same type) in a given scope.
  swap :: (MonadState (([PosToken],Bool),t2) m)=> t   -- ^ The first syntax phrase.
                                               -> t   -- ^ The second syntax phrase.
                                               ->t1   -- ^ The context where the two syntax phrases occur.
                                               ->m t1 -- ^ The result.

instance (Term t)=>Swap HsExpP t  where 
  swap e1 e2  t
    = do  swapInToks e1 e2
          applyTP (full_tdTP (idTP `adhocTP` inExp)) t       -- both full_td and full_bu should wor                       
    where 
      inExp (e ::HsExpP)
       | sameOccurrence e e1                                  
         = return  e2                          
      inExp (e::HsExpP)
       | e == e2 && srcLocs e == srcLocs e2
         = return e1
      inExp x = return x

instance (Term t) => Swap HsPatP t where
  swap p1 p2 t 
   = do swapInToks p1 p2 
        applyTP (full_tdTP (idTP `adhocTP` inPat)) t 
    where
      inPat (p::HsPatP)
       | sameOccurrence p p1                                  
        = return  p2       
      inPat (p::HsPatP)
       | sameOccurrence p p2
         = return p1
      inPat x = return x

instance (Term t) => Swap HsTypeP t where
   swap t1 t2 t 
     = do swapInToks t1 t2
          applyTP (full_tdTP (idTP `adhocTP` inType)) t
     where
       inType (t::HsTypeP)
        | sameOccurrence t t1
          = return t2
       inType (t::HsTypeP)
        | sameOccurrence t t2
         = return t1
       inType t = return t 
-}

class (DeclStartLoc t) =>CanHaveWhereClause t where

 canHaveWhereClause:: t-> Bool

instance CanHaveWhereClause HsMatchP where
 
 canHaveWhereClause t = True

instance CanHaveWhereClause HsDeclP where
 canHaveWhereClause t = isPatBind t 

instance CanHaveWhereClause HsAltP where
  canHaveWhereClause t = True

{-
instance CanHaveWhereClause HsModuleP where
  canHaveWhereClause t = True
-}

instance CanHaveWhereClause HsExpP where
  canHaveWhereClause t = False

instance CanHaveWhereClause HsStmtP where
  canHaveWhereClause t = False

  
class (StartEndLoc t) =>DeclStartLoc  t where
  
  -- | Given a syntax phrase, get the start location of enclosed top-level declaration list.
  declStartLoc:: [PosToken]->t->Maybe RefacTITypeSyn.SimpPos

instance DeclStartLoc HsMatchP where
  declStartLoc toks (HsMatch loc1 name pats rhs ds@(Decs x y))
    = if x/=[] then Just $ fst (getStartEndLoc toks (ghead "declStartLoc" x))
                else Nothing 


instance DeclStartLoc HsDeclP where
  declStartLoc toks (TiDecorate.Dec (HsPatBind loc p rhs ds@(Decs x y)))
     = if x/=[] then Just$ (fst (getStartEndLoc toks (ghead "declStartLoc" x)))
                 else Nothing
  declStartLoc toks _ = Nothing

instance DeclStartLoc HsExpP where
  declStartLoc toks letExp@(TiDecorate.Exp (HsLet ds@(Decs x y) e))
    = if x/=[] then Just $ fst (getStartEndLoc toks (ghead "declStartLoc" x))
                else let (startPos,endPos)=getStartEndLoc toks letExp
                         expToks= getToks (startPos,endPos) toks 
                in Just $ ((tokenPos.(ghead "declStartLoc")) $ dropWhile (not.isIn) expToks)
instance DeclStartLoc HsAltP where
 declStartLoc toks (HsAlt loc p rhs ds@(Decs x y))  
    =if x/=[] then Just $ (fst (getStartEndLoc toks (ghead "declStartLoc" x)))
               else Nothing

instance DeclStartLoc HsStmtP where
 declStartLoc toks (HsLetStmt ds@(Decs x y) stmts)
   = if x/=[] then Just $ fst (getStartEndLoc toks (ghead "declStartLoc" x))
               else Just $ fst (getStartEndLoc toks stmts)   -- Qn: Is this possible?


-- | Return True if syntax phrases t1 and t2 refer to the same one.
sameOccurrence:: (Term t, Eq t) => t -> t -> Bool
sameOccurrence t1 t2
 = t1==t2 && srcLocs t1 == srcLocs t2

{- | The 'HasNameSpace' class. -}
class HasNameSpace t where
   hasNameSpace::t->NameSpace

instance HasNameSpace PNT where
   hasNameSpace (PNT _ Value _)           = ValueName
   hasNameSpace (PNT _ (ConstrOf _ _ ) _) = DataCon
   hasNameSpace (PNT _ (FieldOf _ _ ) _)  = ValueName
   hasNameSpace (PNT _ (MethodOf _  _ _) _)  = ValueName
   hasNameSpace (PNT _ (TypedIds.Class _  _) _)       = ClassName
   hasNameSpace (PNT _ (Type _) _ )       = TypeCon     -- It is also possible that it is a type variable.
   hasNameSpace  _                        = Other       -- We don't care about Assertion & Property so far.

instance HasNameSpace ENT  where
   hasNameSpace (Ent _ _ Value)           = ValueName
   hasNameSpace (Ent _ _ (ConstrOf _ _ )) = DataCon
   hasNameSpace (Ent _ _ (FieldOf _ _ ))  = ValueName
   hasNameSpace (Ent _ _ (MethodOf _ _ _))  = ValueName
   hasNameSpace (Ent _ _ (TypedIds.Class _  _))       = ClassName
   hasNameSpace (Ent _ _ (Type _))        = TypeCon     
   hasNameSpace  _                        = Other       

----------------------------------------------------------------------------------------------
-- |Compose ModuleName from  String.
strToModName::String->ModuleName
strToModName name = if name =="Main" then MainModule "Main.hs"  -- THIS IS BASED ON ASSUMPTION.
                                     else PlainModule name 
-- |From ModuleName to string.
modNameToStr::ModuleName->String
modNameToStr (PlainModule name) = name
modNameToStr (MainModule _)     = "Main"            
                 
-- | From file name to module name.
--fileNameToModName::( )=>String->PFE0MT n i ds ext m ModuleName      

fileNameToModName::(PFE0_IO err m,IOErr err,HasInfixDecls i ds,QualNames i m1 n, Read n,Show n)=>
                   String->PFE0MT n i ds ext m ModuleName         
fileNameToModName fileName = 
  do gf <- getCurrentModuleGraph
     let fileAndMods = [(m,f)|(f,(m,ms))<-gf]
         f = filter (\(m,f) -> f==fileName) fileAndMods
     if f ==[] then error $ "Can't find module name"
                    else return $ (fst.head) f

-- | Return the client module and file names. The client modules of module, say m, are those modules
-- which import m directly or indirectly.

-- clientModsAndFiles::( ) =>ModuleName->PFE0MT n i ds ext m [(ModuleName, String)]
clientModsAndFiles::(PFE0_IO err m,IOErr err,HasInfixDecls i ds,QualNames i m1 n, Read n,Show n)=>
                     ModuleName->PFE0MT n i ds ext m [(ModuleName, String)]
clientModsAndFiles m =
  do gf <- getCurrentModuleGraph
     let fileAndMods = [(m,f)|(f,(m,ms))<-gf]
         g           = (reverseGraph.(map snd)) gf     
         clientMods  = reachable g [m] \\ [m]
         clients     = concatMap (\m'->[(m,f)|(m,f)<-fileAndMods, m==m']) clientMods
     return clients

-- | Return the server module and file names. The server modules of module, say  m, are those modules
-- which are directly or indirectly imported by module m.

--serverModsAndFiles::( )=>ModuleName->PFE0MT n i ds ext m [(ModuleName, String)]

serverModsAndFiles::(PFE0_IO err m,IOErr err,HasInfixDecls i ds,QualNames i m1 n, Read n,Show n)=>
                     ModuleName->PFE0MT n i ds ext m [(ModuleName, String)]
serverModsAndFiles m =
   do gf <- getCurrentModuleGraph
      let fileAndMods = [(m,f)|(f,(m,ms))<-gf]
          g           = (map snd) gf  
          serverMods  = reachable g [m] \\ [m]
          servers     = concatMap (\m'->[(m,f)|(m,f)<-fileAndMods, m==m']) serverMods
      return servers

-- | Return True if the given module name exists in the project.
--isAnExistingMod::( ) =>ModuleName->PFE0MT n i ds ext m Bool


isAnExistingMod::(PFE0_IO err m,IOErr err,HasInfixDecls i ds,QualNames i m1 n, Read n,Show n)=>
                  ModuleName->PFE0MT n i ds ext m Bool

isAnExistingMod m 
  =  do ms<-allModules
        return (elem m ms)

{-Whenever an identifier is imported, the qualified name is imported, whereas the unqualified name
 may or may not be imported. -}

-- | Return all the possible qualifiers for the identifier. The identifier is not inscope if the 
-- result is an empty list.
hsQualifier::PNT                   -- ^ The identifier.
            ->InScopes             -- ^ The in-scope relation.
            ->[ModuleName]         -- ^ The result.
hsQualifier pnt@(PNT pname _ _ ) inScopeRel
  = let r = filter ( \ ( name, nameSpace, modName, qual) -> pNtoName pname == name
                   && hasModName pname == Just modName && hasNameSpace pnt == nameSpace 
                   && isJust qual) $ inScopeInfo inScopeRel
    in  map (\ (_,_,_,qual) -> fromJust qual ) r
                            
                    
-- |Process the inscope relation returned from the parsing and module analysis pass, and 
-- return a list of four-element tuples. Each tuple contains an identifier name, the identifier's namespace
-- info, the identifier's defining module name and its qualifier name. The same identifier may have multiple
-- entries in the result because it may have different qualifiers. This makes it easier to decide whether the
-- identifier can be used unqualifiedly by just checking whether there is an entry for it with the qualifier field
-- being Nothing.
-- 
inScopeInfo::InScopes                                                -- ^ The inscope relation .
           ->[(String, NameSpace, ModuleName, Maybe ModuleName)]     -- ^ The result
inScopeInfo inScopeRel =nub $  map getEntInfo $ relToList inScopeRel 
  where 
     getEntInfo (qual, ent@(Ent modName ident _))
       =(identToName ident, hasNameSpace ent,  modName, getQualifier qual)
       
-- | Process the export relation returned from the parsing and module analysis pass, and 
--   return a list of trhee-element tuples. Each tuple contains an identifier name, the 
--   identifier's namespace info, and the identifier's define module. 
exportInfo::Exports                             -- ^ The export relation.
          -> [(String, NameSpace, ModuleName)]  -- ^ The result
exportInfo exports = nub $ map getEntInfo  exports
  where 
    getEntInfo (_, ent@(Ent modName ident _))
      =(identToName ident, hasNameSpace ent,  modName)

-- | Return True if the identifier is inscope and can be used without a qualifier.          
isInScopeAndUnqualified::String       -- ^ The identifier name.
                       ->InScopes     -- ^ The inscope relation 
                       ->Bool         -- ^ The result.
isInScopeAndUnqualified id inScopeRel
 = isJust $ find (\ (x, _,_, qual) -> x == id && isNothing qual ) $ inScopeInfo inScopeRel
 
--Id is defined in two modules: HsNames.hs (type Id = String) and PosName.hs (type Id = SN HsNames.Id)
identToName (HsVar (SN i _)) = i
identToName (HsCon (SN i _)) = i

-- | Return True if the current module is exported either by default or by specifying the module name in the export.
modIsExported::HsModuleP  -- ^ The AST of the module
               ->Bool     -- ^ The result
modIsExported mod
   = let exps    = hsModExports mod
         modName = hsModName mod
     in if isNothing exps
           then True
           else isJust $ find (==(ModuleE modName)) (fromJust exps)
                      
-- | Return True if the identifier is exported either implicitly or explicitly.         
isExported::PNT         -- ^ The identifier.
           ->Exports    -- ^ The export relation.
           ->Bool       -- ^ The result.
isExported pnt@(PNT pn t1 _) exps
   = if isTopLevelPNT pnt 
       then case hasModName pn of 
               Just modName  -> isJust (find (\(name, nameSpace, modName1) -> name == pNtoName pn
                                         && modName == modName1 && hasNameSpace pnt == nameSpace) $ exportInfo exps)  
               Nothing       -> False
       else False    

-- | Return True if an identifier is explicitly exported by the module.
isExplicitlyExported::PName          -- ^ The identifier
                     ->HsModuleP    -- ^ The AST of the module
                     ->Bool         -- ^ The result
isExplicitlyExported pn mod
  = findEntity pn $ hsModExports mod

{-
causeNameClashInExports::String      -- ^ The identifier name
                        ->HsModuleP  -- ^ The AST of the module
                        ->Exports    -- ^ The export relation of the module
                        ->Bool       -- ^ The result -}

-- Note that in the abstract representation of exps, there is no qualified entities.
causeNameClashInExports  pn newName mod exps 
  = let modNames=nub (concatMap (\(x, Ent modName _ _)->if show x==show newName 
                                                        then [modName]
                                                        else []) exps)
    in (isExplicitlyExported pn mod) && 
        ( any (modIsUnQualifedImported mod) modNames 
            || elem (let (SN modName1 _) =hsModName mod
                     in modName1)  modNames)
 where     
    modIsUnQualifedImported mod modName
     =let imps =hsModImports mod
      in isJust $ find (\(HsImportDecl _ (SN modName1 _) qualify  _ h)->modName==modName1 && (not qualify)) imps

          
-------------------------------------------------------------------------------------------------
{-append an import declaration to the end of the import list in the module, this functions
  modifies both the token stream and the AST
-}

-------------------------------------------------------------------------------------
addImportDecl mod@(HsModule _ _ _ imp decls) moduleName qualify alias hide idNames 
  = do ((toks, _),(v,v1)) <- get
       let (toks1, toks2)
               =if imps' /= []
                   then let (startLoc, endLoc) = startEndLocIncComments toks (last imps')
                            (toks1, toks2)= break (\t->tokenPos t==endLoc) toks
                        in (toks1 ++ [ghead "addImportDecl1" toks2], tail toks2)    
                   else if decls /=[]  
                          then let startLoc = fst $ startEndLocIncComments toks (ghead "addImportDecl1" decls)
                                   (toks1, toks2) = break (\t ->tokenPos t==startLoc) toks  
                               in (toks1,  toks2)
                          else (toks,[])
           before = if toks1/=[] && endsWithNewLn (glast "addImportDecl1" toks1) then "" else "\n"
           after  = if (toks2 /=[] && startsWithNewLn (ghead "addImportDecl1" toks2)) then "" else "\n"         
           colOffset = if imps'==[] && decls==[] 
                        then 1  
                        else getOffset toks
                                $ if imps'/=[] then fst $ startEndLoc toks  (ghead "addImportDecl1" imps') 
                                               else fst $ startEndLoc toks  (ghead "addImportDecl1" decls)
           impToks =tokenise (Pos 0 v1 1) (colOffset-1) True 
                      $ before++(render.ppi) impDecl++"\n" ++ after  --- refactorer this
       (impDecl', _) <- addLocInfo (impDecl,impToks)
       let toks' = toks1++impToks++toks2
       put ((toks',modified), ((tokenRow (glast "addImportDecl1" impToks) - 10,v1)))  -- 10: step ; generalise this.
       return (mod {hsModImports = imp ++ [impDecl']})
  where
     alias' = case alias of 
                  Just m -> Just $ SN (PlainModule m) loc0
                  _      -> Nothing
     impDecl = HsImportDecl loc0 (SN (PlainModule moduleName) loc0) qualify alias' 
                      (if idNames==[] && hide==False 
                          then Nothing
                          else  (Just (hide, map nameToEnt idNames)))  -- what about "Main"
     imps' = imp \\ prelimps
     nameToEnt name = Var (nameToPNT name)
    

---------------------------------------------------------------------------------------

-- | Adding a declaration to the declaration list of the given syntax phrase(so far only adding function\/pattern binding
--  has been tested).  If the second argument is Nothing, then the declaration will be added to the beginning of the
-- declaration list, but after the data type declarations is there is any.
{-addDecl::( ) =>t                -- ^ The AST.
   -> Maybe PName     -- ^ If this is Just, then the declaration will be added right after this identifier's definition.
   ->([HsDeclP], Maybe [PosToken])  -- ^ The declaration to be added, in both AST and Token stream format (optional).
   ->Bool               -- ^ True means the declaration is a toplevel declaration.
   ->m t
-}

addDecl::((MonadState (([PosToken],Bool),(Int,Int)) m), StartEndLoc t, HsDecls t, Printable t)
                    =>t-> Maybe PName 
                    ->([HsDeclP], Maybe [PosToken]) 
                    ->Bool               
                    ->m t

addDecl parent pn (decl, declToks) topLevel
 = if isJust pn 
     then appendDecl parent (fromJust pn) (decl, declToks)
     else if topLevel 
            then addTopLevelDecl (decl, declToks) parent
            else addLocalDecl parent (decl,declToks)
 where

  {- Add a definition to the beginning of the definition declaration list, but after the data type declarations
     if there is any. The definition will be pretty-printed if its token stream is not provided. -}
  addTopLevelDecl (decl, declToks) parent 
    = do let decls = hsDecls parent 
             (decls1,decls2)=break (\x->isFunOrPatBind x || isTypeSig x) decls      
         ((toks,_),(v1, v2))<-get   
         let loc1 = if decls2/=[]  -- there are function/pattern binding decls. 
                    then let ((startRow,_),_) = startEndLocIncComments toks (ghead "addTopLevelDecl"  decls2)
                         in  (startRow, 1)
                    else simpPos0  -- no function/pattern binding decls in the module.
             (toks1, toks2) = if loc1==simpPos0  then (toks, [])
                                 else break (\t->tokenPos t==loc1) toks
             
             declStr = case declToks of 
                        Just ts -> concatMap tokenCon ts
                        Nothing -> prettyprint decl++"\n\n"
             colOffset = if decls ==[] then 1 else getOffset toks $ fst (getStartEndLoc toks (head decls))
             newToks = tokenise (Pos 0 v1 1) colOffset True declStr
             toks' = toks1 ++ newToks ++ toks2
     --    error $ show decl

         put ((toks',modified),((tokenRow (glast "addTopLevelDecl" newToks) -10), v2))                                    
         (decl',_) <- addLocInfo (decl, newToks)
     --    error $ show decl
         return (replaceDecls parent (Decs (decls1++decl'++decls2) ([], [])))

  appendDecl parent pn (decl, declToks)
    = do ((toks,_),(v1, v2))<-get   
         -- error (show parent ++ "----" ++ show pn ++ "-----" ++ show (decl, declToks))
         let (startPos,endPos) = startEndLocIncFowComment toks (ghead "appendDecl1" after) 
             -- divide the toks into three parts.
             (toks1, toks2, toks3) = splitToks' (startPos, endPos) toks 
              --get the toks defining pn
             defToks = dropWhile (\t->tokenPos t /=startPos) toks2
             offset = getOffset toks $ fst (getStartEndLoc toks (ghead "appendDecl2" decls))
             declStr = case declToks of 
                          Just ts -> concatMap tokenCon ts
                          Nothing -> prettyprint decl 
             newToks = tokenise (Pos 0 v1 1) offset True declStr 
             toks' = if  endsWithNewLn  (glast "appendDecl2" toks2)
                      then  toks1++ toks2 ++ (newLnToken: newToks) ++ [newLnToken]++ compressPreNewLns toks3  
                      else  replaceToks toks startPos endPos (defToks++[newLnToken,newLnToken]++newToks)
    --     (decl',_) <- addLocInfo (decl, newToks)
         put ((toks',modified),((tokenRow (glast "appendDecl2" newToks) -10), v2))  
         return (replaceDecls parent (Decs (before ++ [ghead "appendDecl14" after]++ decl++ tail after) ([], [])))        
      where 
        decls = hsDecls parent 
        (before,after) = break (defines pn) decls -- Need to handle the case that 'after' is empty?
        splitToks' (startPos, endPos) toks 
           = let (ts1, ts2, ts3) = splitToks ( startPos, endPos) toks  
                 (ts11, ts12) = break hasNewLn (reverse ts1)
             in (reverse ts12, reverse ts11++ts2, ts3)      

  -- This function need to be tested.
  addLocalDecl parent (newFun, newFunToks)
    =do
        ((toks,_), (v1, v2))<-get  
        let (startPos@(_,startCol),endPos'@(endRow',_))  --endPos' does not include the following newline or comment.
              =if localDecls==[] then startEndLocIncFowComment toks parent    --The 'where' clause is empty
                                 else startEndLocIncFowComment toks localDecls 
            toks1=gtail "addLocalDecl1"  $ dropWhile (\t->tokenPos t/=endPos') toks 
            ts1=takeWhile (\t->isWhite t && ((not.isMultiLineComment) t) && (not.hasNewLn) t)  toks1    
            --nextTokPos is only used to test whether there is a 'In' or a nested comment. 
            nextTokPos= case (dropWhile (\t->isWhite t && ((not.isMultiLineComment) t) && (not.hasNewLn) t) toks1) of
                           [] -> simpPos0 
                           l  -> (tokenPos.ghead "addLocalFunInToks") l 
            needNewLn=if nextTokPos==simpPos0  --used to decide whether add a new line character before a introduced fun.
                      then if toks1==[] then True
                                        else (not.endsWithNewLn) (last ts1) 
                      else endRow'==fst nextTokPos 
            --endPos@(endRow,_)=if ts1==[] then endPos'
            --                             else tokenPos (last ts1)
            offset = if localDecls == [] then getOffset toks startPos + 4 else getOffset toks startPos
            newToks = tokenise (Pos 0 v1 1) offset True 
                          $ if needNewLn then "\n"++newSource else newSource++"\n"
            oldToks'=getToks (startPos,endPos') toks
            toks'=replaceToks toks startPos endPos' (oldToks'++newToks)           
        (newFun',_) <- addLocInfo (newFun, newToks) -- This function calles problems because of the lexer.
        put ((toks',modified),((tokenRow (glast "appendDecl2" newToks) -10), v2))  
        return (replaceDecls parent (Decs (hsDecls parent ++ newFun') ([], [])))
    where
         localDecls = hsDecls parent
        
         newSource  = if localDecls == []
                      then "where\n"++ concatMap (\l-> "  "++l++"\n") (lines newFun')
                      else newFun'
            where
            newFun' = case newFunToks of 
                           Just ts -> concatMap tokenCon ts 
                           Nothing -> prettyprint newFun 

-- | Remove the type signature that defines the given identifier's type from the declaration list.
{-rmTypeSig::(MonadState (([PosToken],Bool),t1) m)
            => PName       -- ^ The identifier whose type signature is to be removed.
            ->[HsDeclP]    -- ^ The declaration list
            ->m [HsDeclP]  -- ^ The result -}

rmTypeSig pn  t = applyTP (full_tdTP (idTP `adhocTP` inDecls)) t
  where 
   inDecls (decls::[HsDeclP])
      | snd (break (definesTypeSig pn) decls) /=[] 
     = do ((toks,_), others) <- get
          let (decls1,decls2)= break  (definesTypeSig pn) decls
              (toks',decls')=
               let sig@(TiDecorate.Dec (HsTypeSig loc is c tp))=ghead "rmTypeSig" decls2  -- as decls2/=[], no problem with head 
                   (startPos,endPos)=getStartEndLoc toks sig 
               in if length is>1  
                     then let newSig=(TiDecorate.Dec (HsTypeSig loc (filter (\x-> (pNTtoPN x)/=pn) is) c tp))
                              pnt = ghead "rmTypeSig" (filter (\x-> pNTtoPN x == pn) is)
                              (startPos1, endPos1) = let (startPos1', endPos1') = getStartEndLoc toks pnt
                                                     in if fromJust (elemIndex pnt is) >0
                                                        then extendForwards toks startPos1' endPos1' isComma
                                                        else extendBackwards toks startPos1' endPos1' isComma
                          in (deleteToks toks startPos1 endPos1,(decls1++[newSig]++tail decls2))
                     else  ((deleteToks toks startPos endPos),(decls1++tail decls2)) 
          put ((toks',modified),others)
          return decls' 
   inDecls x = return x

-- |Comment out the type signature that defines pn's type in the token stream and remove it from the AST. 
commentOutTypeSig::(MonadState (([PosToken],Bool),t1) m)
            => PName       -- ^ The identifier.
            ->[HsDeclP]    -- ^ The deckaration list.
            ->m [HsDeclP]  -- ^ The result.
commentOutTypeSig pn decls  
 =let (decls1,decls2)=break  (definesTypeSig pn) decls
  in if decls2/=[] then    --There is a type signature for pn
       do ((toks,_),others)<-get   
          let (toks',decls')=
               let sig@(TiDecorate.Dec (HsTypeSig loc is c tp))=ghead "rmTypeSig" decls2  -- as decls2/=[], no problem with head 
               in if length is>1   --This type signature also defines the type of  variables other than pn
                     then let newSig=(TiDecorate.Dec (HsTypeSig loc (filter (\x-> (pNTtoPN x)/=pn) is) c tp))
                              pnt = ghead "commentTypeSig" $ filter (\x->pNTtoPN x==pn) is 
                              (startPos,endPos) = getStartEndLoc toks pnt 
                          in ((commentToks (startPos, endPos) toks),(decls1++[newSig]++tail decls2))
                     else let  (startPos,endPos)=getStartEndLoc toks sig 
                          in  ((commentToks  (startPos, endPos) toks),(decls1++tail decls2)) 
          put ((toks',modified),others)
          return decls' 
      else return decls  



-- | Remove the declaration (and the type signature is the second parameter is True) that defines the given identifier
-- from the declaration list.
{-
rmDecl::(MonadState (([PosToken],Bool),t1) m)
        =>PName       -- ^ The identifier whose definition is to be removed.
        ->Bool        -- ^ True means including the type signature.
        ->[HsDeclP]   -- ^ The declaration list.
        -> m [HsDeclP]-- ^ The result.
-}
rmDecl pn incSig t = applyTP (once_tdTP (failTP `adhocTP` inDecls)) t
  where 
    inDecls (decls::[HsDeclP])
      | snd (break (defines pn) decls) /=[] 
      = do let (decls1, decls2) = break (defines pn) decls
               decl = ghead "rmDecl" decls2
           -- error $ (render.ppi) t -- ecl ++ (show decl) 
           case isTopLevelPN  pn of
                     True   -> if incSig then rmTopLevelDecl decl =<< rmTypeSig pn decls
                                         else rmTopLevelDecl decl decls
                     False  -> if incSig then rmLocalDecl decl =<< rmTypeSig pn decls 
                                         else rmLocalDecl decl decls
    inDecls x = mzero 
    rmTopLevelDecl decl decls 
      =do ((toks,_),others)<-get   
          let (startLoc, endLoc)=startEndLocIncComments toks decl      
              toks'=deleteToks toks startLoc endLoc
          put ((toks',modified),others)
          return (decls \\ [decl]) 


  {- The difference between removing a top level declaration and a local declaration is:
     if the local declaration to be removed is the only declaration in current declaration list, 
     then the 'where'/ 'let'/'in' enclosing this declaration should also be removed.
     Whereas, when a only top level decl is removed, the 'where' can not be removed.
   -}
-- |Remove a location declaration that defines pn.
    rmLocalDecl decl decls
     =do ((toks,_),others)<-get   
         let (startPos,endPos)=getStartEndLoc toks decl   --startEndLoc toks decl  
             (startPos',endPos')=startEndLocIncComments toks decl       
             --(startPos',endPos')=startEndLocIncFowComment toks decl 
             toks'=if length decls==1  --only one decl, which means the accompaning 'where',
                                       --'let' or'in' should be removed too.
                   then let (toks1,toks2)=break (\t->tokenPos t==startPos) toks --devide the token stream.
                              --get the  'where' or 'let' token
                            rvToks1=dropWhile (not.isWhereOrLet) (reverse toks1)
                            --There must be a 'where' or 'let', so rvToks1 can not be empty.
                            whereOrLet=ghead "rmLocalFunPatBind:whereOrLet" rvToks1 
                            --drop the 'where' 'or 'let' token
                            toks1'=takeWhile (\t->tokenPos t/=tokenPos whereOrLet) toks1
                            --remove the declaration from the token stream.
                            toks2'=gtail "rmLocalDecl" $ dropWhile (\t->tokenPos t/=endPos') toks2
                            --get the remained tokens after the removed declaration.
                            remainedToks=dropWhile isWhite toks2'
                        in if remainedToks==[] 
                             then --the removed declaration is the last decl in the file.
                                  (compressEndNewLns toks1'++ compressPreNewLns toks2') 
                             else if --remainedToks/=[], so no problem with head.
                                    isIn (ghead "rmLocalDecl:isIn"  remainedToks)  
                                         || isComma (ghead "rmLocalDecl:isComma" remainedToks) 
                                        --There is a 'In' after the removed declaration.
                                   then if isWhere whereOrLet
                                           then deleteToks toks (tokenPos whereOrLet) endPos'
                                           else deleteToks toks (tokenPos whereOrLet) 
                                                   $ tokenPos (ghead "rmLocalDecl:tokenPos" remainedToks)
                                        --delete the decl and adjust the layout                      
                                   else if isCloseSquareBracket (ghead "rmLocalDecl:isCloseSquareBracker" remainedToks) &&
                                           (isBar.(ghead "rmLocalDecl:isBar")) (dropWhile isWhite (tail rvToks1))
                                         then deleteToks toks (tokenPos((ghead "rmLocalDecl") 
                                                        (dropWhile isWhite (tail rvToks1)))) endPos'
                                         else deleteToks toks (tokenPos whereOrLet) endPos' 
                        --there are more than one decls
                   else  deleteToks toks startPos' endPos'
         put ((toks',modified),others)  --Change the above endPos' to endPos will not delete the following comments.
         return $ (decls \\ [decl])

{- ********* IMPORTANT : THIS FUNCTION SHOULD BE UPDATED TO THE NEW TOKEN STREAM METHOD ****** -}
-- | Duplicate a functon\/pattern binding declaration under a new name right after the original one.
duplicateDecl::(MonadState (([PosToken],Bool),t1) m)
                 =>[HsDeclP]            -- ^ The declaration list
                 ->PName                -- ^ The identifier whose definition is going to be duplicated
                 ->String               -- ^ The new name
                 ->m [HsDeclP]          -- ^ The result
{-there maybe fun/simple pattern binding and type signature in the duplicated decls
  function binding, and type signature are handled differently here: the comment and layout
  in function binding are preserved.The type signature is output ted by pretty printer, so
  the comments and layout are NOT preserved.
 -}
duplicateDecl decls pn newFunName
 = do ((toks,_), others)<-get   
      let (startPos, endPos) =startEndLocIncComments toks funBinding  
          {-take those tokens before (and include) the function binding and its following
            white tokens before the 'new line' token. (some times the function may be followed by 
            comments) -}
          toks1 = let (ts1, ts2) =break (\t->tokenPos t==endPos) toks in ts1++[ghead "duplicateDecl" ts2]
          --take those token after (and include) the function binding
          toks2 = dropWhile (\t->tokenPos t/=startPos || isNewLn t) toks
      put((toks2,modified), others)
      --rename the function name to the new name, and update token stream as well
      funBinding'<-renamePN pn Nothing newFunName True funBinding
      --rename function name in type signature  without adjusting the token stream
      typeSig'  <- renamePN pn Nothing newFunName False typeSig
      ((toks2,_), others)<-get    
      let offset = getOffset toks (fst (startEndLoc toks funBinding))
          newLineTok = if toks1/=[] && endsWithNewLn (glast "doDuplicating" toks1)
                         then [newLnToken]
                         else [newLnToken,newLnToken] 
          toks'= if typeSig/=[] 
                 then let offset = tokenCol ((ghead "doDuplicating") (dropWhile (\t->isWhite t) toks2))
                          sigSource = concatMap (\s->replicate (offset-1) ' '++s++"\n")((lines.render.ppi) typeSig')
                          t = mkToken Whitespace (0,0) sigSource  
                      in  (toks1++newLineTok++[t]++(whiteSpacesToken (0,0) (snd startPos-1))++toks2)
                 else (toks1++newLineTok++(whiteSpacesToken (0,0) (snd startPos-1))++toks2) 
      put ((toks',modified),others)
      return (typeSig'++funBinding')
     where 
       declsToDup = definingDecls [pn] decls True False    
       funBinding = filter isFunOrPatBind declsToDup     --get the fun binding.
       typeSig    = filter isTypeSig declsToDup      --get the type signature.   


------------------------------------------------------------------------------

-- | Add identifiers to the export list of a module. If the second argument is like: Just p, then do the adding only if p occurs
-- in the export list, and the new identifiers are added right after p in the export list. Otherwise the new identifiers are add
-- to the beginning of the export list. In the case that the export list is emport, then if the third argument is True, then create
-- an explict export list to contain only the new identifiers, otherwise do nothing.
{-
addItemsToExport::( )
                 => HsModuleP                           -- The module AST.    
                   -> Maybe PName                       -- The condtion identifier.
                   -> Bool                              -- Create an explicit list or not
                   -> Either [String] [HsExportEntP]    -- The identifiers to add in either String or HsExportEntP format.
                   -> m HsModuleP                       -- The result.
-}

addItemsToExport::(MonadState (([PosToken],Bool), t1) m)
                 => HsModuleP                           -- The module AST.    
                   -> Maybe PName                       -- The condtion identifier.
                   -> Bool                              -- Create an explicit list or not
                   -> Either [String] [HsExportEntP]    -- The identifiers to add in either String or HsExportEntP format.
                   -> m HsModuleP                       -- The result.


addItemsToExport mod _  _ (Left [])  = return mod
addItemsToExport mod _  _ (Right []) = return mod
addItemsToExport mod@(HsModule loc modName exps imps ds) (Just pn) _ ids
  =  case exps  of
       Just ents ->let (e1,e2) = break (findEntity pn) ents
                   in if e2 /=[]  
                        then do ((toks,_),others)<-get   
                                let e = (ghead "addVarItemInExport" e2)
                                    es = case ids of 
                                          (Left is' ) ->map (\x-> (EntE (Var (nameToPNT x)))) is'
                                          (Right es') -> es' 
                                let (_,endPos) = getStartEndLoc toks e
                                    (t, (_,s)) = ghead "addVarItemInExport" $ getToks (endPos,endPos) toks
                                    newToken = mkToken t endPos (s++","++ showEntities (render.ppi) es) 
                                    toks' = replaceToks toks endPos endPos [newToken]
                                put ((toks',modified),others)                                   
                                return (HsModule loc modName (Just (e1++(e:es)++tail e2)) imps ds)
                        else return mod                     
       Nothing   -> return mod   

addItemsToExport mod@(HsModule _ _ (Just ents) _ _) Nothing createExp ids
    = do ((toks,_),others)<-get
         let es = case ids of 
                    (Left is' ) ->map (\x-> (EntE (Var (nameToPNT x)))) is'
                    (Right es') -> es'
             (t, (pos,s))=fromJust $ find isOpenBracket toks  -- s is the '('
             newToken = if ents /=[] then  (t, (pos,(s++showEntities (render.ppi) es++",")))
                                     else  (t, (pos,(s++showEntities (render.ppi) es)))
             pos'= simpPos pos
             toks' = replaceToks toks pos' pos' [newToken]
         put ((toks',modified),others)  
         return mod {hsModExports=Just (es++ ents)}

addItemsToExport mod@(HsModule _  (SN modName (SrcLoc _ c row col))  Nothing _ _)  Nothing createExp ids
  =case createExp of 
       True ->do ((toks,_),others)<-get
                 let es = case ids of 
                               (Left is' ) ->map (\x-> (EntE (Var (nameToPNT x)))) is'
                               (Right es') -> es'
                     pos = (row,col)
                     newToken = mkToken Varid pos (modNameToStr modName++ "(" 
                                         ++ showEntities (render.ppi) es++")")
                     toks' = replaceToks toks pos pos [newToken]
                 put  ((toks', modified), others)       
                 return mod {hsModExports=Just es}
       False ->return mod               

-- | Add identifiers (given by the third argument) to the explicit entity list in the declaration importing the
--   specified module name. The second argument serves as a condition: if it is like : Just p, then do the adding 
--   the if only 'p' occurs in the entity list; if it is Nothing, then do the adding as normal. This function
--   does nothing if the import declaration does not have an explicit entity list.
{-
addItemsToImport::( )
                 =>ModuleName                  -- ^ The imported module name.
                 ->Maybe PName                 -- ^ The condition identifier.
                 ->Either [String] [EntSpecP]  -- ^ The identifiers to add in either String or EntSpecP format.
                 ->t                           -- ^ The given syntax phrase.
                 ->m t                         -- ^ The result.
-}

addItemsToImport::(Term t,MonadState (([PosToken],Bool),t1) m) 
                 =>ModuleName                  -- ^ The imported module name.
                 ->Maybe PName                 -- ^ The condition identifier.
                 ->Either [String] [EntSpecP]  -- ^ The identifiers to add in either String or EntSpecP format.
                 ->t                           -- ^ The given syntax phrase.
                 ->m t                         -- ^ The result.

addItemsToImport serverModName pn (Left [])  t = return t 
addItemsToImport serverModName pn (Right []) t = return t
addItemsToImport serverModName pn ids t
 =applyTP (full_buTP (idTP `adhocTP` inImport)) t
  where 
    inImport (imp@(HsImportDecl loc m@(SN modName _) qual  as h):: HsImportDeclP)
      | serverModName == modName && (if isJust pn then findPN (fromJust pn) h else True)
       = case h of
           Nothing        -> return imp                     
           Just (b, ents) -> do let ents'=case ids of
                                          Left  is'  -> map (\x-> Var (nameToPNT x)) is'
                                          Right es   -> es
                                ((toks,_),others)<-get
                                let (_,endPos)=getStartEndLoc toks (glast "addItemsToImport" ents)
                                    (t,(_,s))=ghead "addItemsToImport" $ getToks (endPos,endPos) toks
                                    newToken = mkToken t endPos (s++","++showEntities (render.ppi) ents')
                                    toks'=replaceToks toks endPos endPos [newToken]
                                put ((toks',modified),others)
                                return (HsImportDecl loc m qual as (Just (b, ents++ents')))
    inImport imp = return imp

-- | add items to the hiding list of an import declaration which imports the specified module.
addHiding::(MonadState (([PosToken],Bool),t1) m) 
            =>ModuleName           -- ^ The imported module name
            ->HsModuleP            -- ^ The current module
            ->[PName]              -- ^ The items to be added
            ->m HsModuleP          -- ^ The result 
addHiding serverModName mod pns
   = applyTP (full_tdTP (idTP `adhocTP` inImport)) mod
  where 
    inImport (imp@(HsImportDecl loc (SN modName _) qual  as h)::HsImportDeclP)
      | serverModName == modName  && not qual
       = case h of
           Nothing ->do ((toks,_),others)<-get  
                        let (_,endPos)=getStartEndLoc toks imp
                            (t,(_,s)) = ghead "addHiding" $ getToks (endPos,endPos) toks 
                            newToken=mkToken t endPos (s++" hiding ("++showEntities pNtoName pns++")")
                            toks'=replaceToks toks endPos endPos [newToken]
                        put ((toks',modified),others)    
                        return (replaceHiding imp (Just (True, map mkNewEnt pns )))
           Just (True, ents) ->do ((toks,_),others)<-get  
                                  let (_,endPos)=getStartEndLoc toks imp
                                      (t, (_,s))=ghead "addHiding"  $ getToks (endPos,endPos) toks
                                      newToken=mkToken t endPos (","++showEntities pNtoName pns ++s)
                                      toks'=replaceToks toks endPos endPos [newToken]
                                  put ((toks',modified),others) 
                                  return (replaceHiding imp  (Just (True, (map mkNewEnt  pns)++ents))) 
           Just (False, ent)  -> return imp 
    inImport x = return x

    mkNewEnt pn = (Var (PNT pn Value (N (Just loc0))))
    replaceHiding (HsImportDecl loc modName qual as h) h1 = HsImportDecl loc modName qual as h1    


-- | Remove those specified items from the entity list in the import declaration.
{-
 rmItemsFromImport::( ) 
                   =>HsModuleP    -- ^ The module AST
                   ->[PName]      -- ^ The items to be removed
                   ->m HsModuleP  -- ^ The result
-}


rmItemsFromImport::(MonadState (([PosToken],Bool),t1) m) 
                   =>HsModuleP    -- ^ The module AST
                   ->[PName]      -- ^ The items to be removed
                   ->m HsModuleP  -- ^ The result


rmItemsFromImport mod pns
  = applyTP (full_buTP (idTP `adhocTP` inImport)) mod
   where 
     inImport (imp@(HsImportDecl loc modName qual  as h)::HsImportDeclP)
      | any (flip findEntity imp) pns
       = case h of
           Just (b, ents) ->
             do let matchedEnts=findEnts pns ents
                if  matchedEnts==[] 
                  then return imp
                  else if length matchedEnts == length ents   
                         then do ((toks,_),others)<-get  
                                 let (startPos,endPos)=getStartEndLoc toks ents
                                     toks'=deleteToks toks startPos endPos
                                 put ((toks',modified),others)
                                 return (HsImportDecl loc modName qual as (Just (b,[])))
                         else do ((toks,_),others)<-get  
                                 let remainedEnts=concatMap (\pn->filter (not.match pn) ents) pns 
                                     toks'=foldl deleteEnt toks $ map (getStartEndLoc toks) matchedEnts
                                 put ((toks',modified),others)
                                 return (HsImportDecl loc modName qual as (Just (b, remainedEnts)))
           _ ->return imp 
     inImport x = return x
   
     findEnts pns ents =nub $ concatMap (\pn->filter (match pn) ents) pns

     -- this function does not check this sub entities of the ListSubs. any problems?
     match::PName -> EntSpec PNT ->Bool
     match pn (Var pnt) = pNTtoPN pnt == pn
     match pn (Abs pnt) = pNTtoPN pnt == pn
     match pn (AllSubs pnt) = pNTtoPN pnt == pn
     match pn (ListSubs pnt _) = pNTtoPN pnt == pn

-- | Remove the sub entities of a type constructor or class from the export list.
rmSubEntsFromExport::(MonadState (([PosToken],Bool),(Int,Int)) m)
                     =>PName       -- ^ The type constructor or class name
                     ->HsModuleP   -- ^ The module AST
                     ->m HsModuleP -- ^ The result
rmSubEntsFromExport typeCon 
  = applyTP (full_buTP (idTP `adhocTP` inEntSpec))
  where
   inEntSpec (ent@(AllSubs pnt)::EntSpec PNT)
     | pNTtoPN pnt == typeCon 
      =do (ent', _)<-updateToks ent (Abs pnt) prettyprint
          return ent'
   inEntSpec (ent@(ListSubs pnt _))
     | pNTtoPN pnt == typeCon 
     = do (ent', _) <- updateToks ent (Abs pnt) prettyprint
          return ent'
   inEntSpec ent = return ent
     
---------------------------------------------------------------------------------------
-- | Remove the specified entities from the module's exports. The entities can be specified in either of two formats:
-- i.e. either specify the module names and identifier names to be removed, so just given the exact AST for these entities.
{-rmItemsFromExport::( ) 
                   =>HsModuleP                                      -- ^ The module AST.
                    ->Either ([ModuleName],[PName]) [HsExportEntP]  -- ^ The entities to remove. 
                                                                    
                    ->m HsModuleP                                   -- ^ The result.
-}
rmItemsFromExport::(MonadState (([PosToken],Bool),t1) m) 
                   =>HsModuleP                                      -- ^ The module AST.
                    ->Either ([ModuleName],[PName]) [HsExportEntP]  -- ^ The entities to remove. 
                                                                    
                    ->m HsModuleP                                   -- ^ The result.

rmItemsFromExport mod@(HsModule loc modName exps imps ds)  (Left (modNames, pns))
  =if isNothing exps
     then return mod
     else do let ents =findEnts (modNames, pns) (fromJust exps)
             rmItemsFromExport mod (Right ents) 
  where   
    findEnts (modNames, pns) ents
      =let ms = concatMap (\m ->filter (\e -> case e of 
                                         ModuleE (SN m' _) -> m==m'
                                         EntE e'    -> False) ents) modNames 
           es =concatMap (\pn->filter (\e ->case e of 
                                            ModuleE _ -> False
                                            EntE e'    -> match pn e') ents) pns 
       in (ms++es)
    match::PName -> EntSpec PNT ->Bool
    match pn (Var pnt) = pNTtoPN pnt == pn
    match pn (Abs pnt) = pNTtoPN pnt == pn
    match pn (AllSubs pnt) = pNTtoPN pnt == pn
    match pn (ListSubs pnt _) = pNTtoPN pnt == pn

rmItemsFromExport mod@(HsModule loc modName exps@(Just es) imps ds) (Right ents)
  = do exps'<- if ents==[] 
                  then return exps
                  else if length ents == length es 
                         then do ((toks,_),others)<-get             
                                 let (startPos,endPos) = getStartEndLoc toks ents
                                     toks'= deleteToks toks startPos endPos
                                 put ((toks',modified),others)
                                 return (Just [] )  -- should not remove the empty bracket!!!
                         else do ((toks,_),others)<-get 
                                 let toks' = foldl deleteEnt toks $ map (getStartEndLoc toks) ents
                                 put ((toks',modified),others)
                                 return (Just (es \\ ents))                 
       return (HsModule loc modName exps' imps ds)
rmItemsFromExport mod _ = return mod

--This function is only used by this module, and should not be exported.
deleteEnt toks (startPos, endPos)
  = let (toks1,toks2)=break (\t->tokenPos t==startPos) toks
        previousTok=ghead "deleteEnt" $ dropWhile isWhiteSpace $ reverse toks1
        toks' = dropWhile isWhiteSpace $ gtail "deleteEnts" $ dropWhile (\t->tokenPos t/=endPos) toks2
        nextTok = ghead "deleteEnt" toks'
        startPos'=if isComma previousTok && (not (isComma nextTok)) then tokenPos previousTok else startPos
    in if isComma nextTok                    
         then let remainedToks = tail toks' 
              in if remainedToks /= [] 
                   then let whites = takeWhile isWhiteSpace remainedToks
                        in if whites /= [] then deleteToks toks startPos' (tokenPos (last whites))
                                           else deleteToks toks startPos' (tokenPos nextTok)
                   else deleteToks toks startPos' (tokenPos nextTok)
         else deleteToks toks startPos' endPos  



--------------------------------TRY TO REMOVE THIS FUNCTION------------------------------
{-                                    
moveDecl::(CanHaveWhereClause t,DeclStartLoc t, Term t,Printable t,MonadPlus m, 
           MonadState (([PosToken],Bool),(Int, Int)) m)
     => [PName]        -- ^ The identifier(s) whose defining declaration is to be moved. List is used to handle pattern bindings where multiple identifiers are defined.
     -> t              -- ^ The syntax phrase where the declaration is going to be moved to.
     -> Bool           -- ^ True mean the function\/pattern binding being moved is going to be at the same level with t. Otherwise it will be a local declaration of t.
     -> [HsDeclP]      -- ^ The declaration list where the definition\/pattern binding originally exists.
     -> Bool           -- ^ True means the type signature will not be discarded.
     -> m t            -- ^ The result.
-}                    
moveDecl pns dest sameLevel decls incSig
   = do ((ts,_),_)<-get  
        let defToks' =(getDeclToks (ghead "moveDecl:0" pns) True decls ts)      
            defToks  =whiteSpaceTokens (tokenRow (ghead "moveDecl" defToks'),0)
                                       -- do not use tokenCol here. should count the whilte spaces.
                                       (tokenCol (ghead "moveDecl2" defToks') -1) ++ defToks'
            movedDecls = definingDecls pns decls True False
        decls'<-rmDecl (ghead "moveDecl3"  pns) False =<<foldM (flip rmTypeSig) decls pns
        addDecl dest Nothing (movedDecls, Just defToks) False

---------------------------------------------------------------------------------------------

-- |Parse a Haskell source files, and returns a four-element tuple. The first element in the result is the inscope 
-- relation, the second element is the export relation, the third is the type decorated AST of the module and the forth element is
-- the token stream of the module.
{- 
parseSourceFile:: ( ) =>FilePath
                      ->m (InScopes,Exports,HsModuleP,[PosToken])  
-}

parseSourceFile filename 
   = do
        
         modle <- fileNameToModName filename        
         (inscps, exps, mod, tokList) <- (checkScope @@ parseSourceFile') filename 
        
         mod' <- typeCheckMod [modle]
         -- map the normal AST over the typed AST preserving type info
         mod2 <- mapASTOverTAST mod mod'
        
         return (inscps, exps, mod2, tokList)
  where 
   checkScope (ts,(((wm,_),mod),refs))
     = check (checkRefs refs) >> return (inscpRel wm, exports wm, mod, expandNewLnTokens ts) 

   check [] = done
   check errs = fail $ pp $ "Scoping errors" $$ vcat errs   
   
   typeCheckMod [mod] = do
         x <- typeCheck (Just [mod])         
         let y = [map snd tms | (_,(x,(tms,y))) <- x]
        -- let y' = map snd y
        
         
         
         return (head (head y))
         
newProj args = do 
             newProject     
             addPaths True args
addFile fileName 
 = addPaths False fileName 

chase fileNames
 = findMissing fileNames

--preprocssing the token stream to expand the white spaces to individual tokens.
expandNewLnTokens::[PosToken]->[PosToken]
expandNewLnTokens ts = concatMap expand ts
  where
    expand tok@(Whitespace,(pos,s)) = doExpanding pos s                
    expand x = [x]

    doExpanding pos [] =[]
    doExpanding pos@(Pos c row col) (t:ts)
      = case t of 
           '\n'  -> (Whitespace, (pos,[t])):(doExpanding (Pos c (row+1) 1) ts)
           _     -> (Whitespace, (pos,[t])):(doExpanding (Pos c row (col+1)) ts)

------------------------------------------------------------------------------------------------


-- | Write refactored program source to files. 
{-
writeRefactoredFiles::Bool   -- ^ True means the current refactoring is a sub-refactoring
         ->[((String,Bool),([PosToken],HsModuleP))]  --  ^ String: the file name; Bool: True means the file has been modified.[PosToken]: the token stream; HsModuleP: the module AST.
         -> m ()  
-}      
writeRefactoredFiles (isSubRefactor::Bool) (files::[((String,Bool),([PosToken], HsModuleP))]) 
  = do let modifiedFiles = filter (\((f,m),_)->m==modified) files
       addToHistory isSubRefactor $ map (fst.fst) modifiedFiles
       mapM_ modifyFile modifiedFiles
       mapM_ writeTestDataForFile files   -- This should be removed for the release version.
       {-   -- the 'writeTestDataForFile' causes a 'stack overflow' problem, when applying refactorings to
          -- large-scale programs,and the possible reason might be lazy evaluation and the huge size of AST.
         -}
     where
       modifyFile ((fileName,_),(ts,mod)) = do
           --let source =(render.ppi) mod 
           let source = concatMap (snd.snd) ts
           seq (length source) $ writeHaskellFile fileName source
           editorCmds <-getEditorCmds 
           MT.lift $ sendEditorModified editorCmds fileName        
       writeTestDataForFile ((fileName,_),(ts,mod)) = do
           let source=concatMap (snd.snd) ts
           seq (length source) $ writeFile (createNewFileName "_TokOut" fileName) source 
           writeHaskellFile (createNewFileName "AST" fileName) ((render.ppi.rmPrelude) mod)   
       createNewFileName str fileName 
          =let (name, posfix)=span (/='.') fileName
           in (name++str++posfix) 

--------------------------------------------------------------------------------------- 
-----Remove the 'Prelude' imports added by Programatica------------------------------
rmPrelude::HsModuleP->HsModuleP
rmPrelude (HsModule s m e is ds) = HsModule s m e (is \\ prelimps) ds

prelimps = [HsImportDecl loc0  (SN (PlainModule "Prelude") loc0)  True Nothing Nothing,
            HsImportDecl loc0  (SN (PlainModule "Prelude") loc0) False Nothing Nothing]
    

-- | Return True if a string is a lexically  valid variable name.
isVarId::String->Bool
isVarId id =RefacTypeUtils.isId id && isSmall (ghead "isVarId" id) 
     where isSmall c=isLower c || c=='_'

-- | Return True if a string is a lexically valid constructor name.
isConId::String->Bool
isConId id =RefacTypeUtils.isId id && isUpper (ghead "isConId" id)

-- | Return True if a string is a lexically valid operator name.
isOperator::String->Bool
isOperator id = id /= [] && isOpSym (ghead "isOperator" id) &&
                isLegalOpTail (tail id) && not (isReservedOp id)
   where

    isOpSym id = elem id opSymbols
       where opSymbols = ['!', '#', '$', '%', '&', '*', '+','.','/','<','=','>','?','@','\'','^','|','-','~']

    isLegalOpTail tail = all isLegal tail
       where isLegal c = isOpSym c || c==':'

    isReservedOp id = elem id reservedOps
       where reservedOps = ["..", ":","::","=","\"", "|","<-","@","~","=>"]

{-Returns True if a string lexically is an identifier. *This function should not be exported.*
-}  
isId::String->Bool
isId id = id/=[] && isLegalIdTail (tail id) && not (isReservedId id)
  where
    isLegalIdTail tail=all isLegal tail
        where isLegal c=isSmall c|| isUpper c || isDigit c || c=='\''

    isReservedId id=elem id reservedIds 
      where reservedIds=["case", "class", "data", "default", "deriving","do","else" ,"if",
                         "import", "in", "infix","infixl","infixr","instance","let","module",
                         "newtype", "of","then","type","where","_"]

    isSmall c=isLower c || c=='_'

-----------------------------------------------------------------------------
-- |Return True if a PName is a toplevel PName.
isTopLevelPN::PName->Bool
isTopLevelPN (PN i (G _ _ _))=True
isTopLevelPN _ =False

-- |Return True if a PName is a local PName.
isLocalPN::PName->Bool
isLocalPN (PN i (UniqueNames.S _))=True
isLocalPN _ =False

-- |Return True if a PName is a qualified PName.
isQualifiedPN::PName->Bool
isQualifiedPN (PN (Qual mod id) _)=True
isQualifiedPN _ =False 

-- |Return True if an PNT is a toplevel PNT.
isTopLevelPNT::PNT->Bool
isTopLevelPNT = isTopLevelPN.pNTtoPN

-- |Return True if a PName is a function\/pattern name defined in t.
isFunOrPatName::(Term t)=>PName->t->Bool
isFunOrPatName pn 
   =isJust.(applyTU (once_tdTU (failTU `adhocTU` worker)))
     where
        worker (decl::HsDeclP)
           | defines pn decl=Just True
        worker _ =Nothing

-- |Return True if a PNT is a function name defined in t.
isFunPNT::(Term t)=>PNT -> t -> Bool
isFunPNT pnt t = isFunName (pNTtoPN pnt) t 

isFunName::(Term t)=>PName->t->Bool
isFunName pn 
   =isJust.(applyTU (once_tdTU (failTU `adhocTU` worker)))
     where
        worker (decl::HsDeclP)
           | isFunBind decl && defines pn decl =Just True
        worker _ =Nothing

-- |Return True if a PName is a pattern name defined in t.
isPatName::(Term t)=>PName->t->Bool
isPatName pn 
   =isJust.(applyTU (once_tdTU (failTU `adhocTU` worker)))
     where
        worker (decl::HsDeclP)
           | isPatBind decl && defines pn decl =Just True
        worker _ =Nothing
-------------------------------------------------------------------------------
-- | Return True if a PNT is a type constructor.
isTypeCon :: PNT -> Bool
isTypeCon (PNT pn (Type typeInfo) _) = defType typeInfo == Just TypedIds.Data
isTypeCon _ = False 

-- | Return True if a declaration is a type signature declaration.
isTypeSig ::HsDeclP->Bool
isTypeSig (TiDecorate.Dec (HsTypeSig loc is c tp))=True
isTypeSig _=False

-- | Return True if a declaration is a function definition.
isFunBind::HsDeclP->Bool
isFunBind (TiDecorate.Dec (HsFunBind loc matches))=True
isFunBind _ =False

-- | Returns True if a declaration is a pattern binding.
isPatBind::HsDeclP->Bool
isPatBind (TiDecorate.Dec (HsPatBind _ _ _ _))=True
isPatBind _=False

-- | Return True if a declaration is a pattern binding which only defines a variable value.
isSimplePatBind::HsDeclP->Bool
isSimplePatBind decl=case decl of
     TiDecorate.Dec (HsPatBind _ p _ _)->patToPN p /=defaultPN
     _ ->False

-- | Return True if a declaration is a pattern binding but not a simple one.
isComplexPatBind::HsDeclP->Bool
isComplexPatBind decl=case decl of
     TiDecorate.Dec (HsPatBind _ p _ _)->patToPN p ==defaultPN
     _ -> False

-- | Return True if a declaration is a function\/pattern definition.
isFunOrPatBind::HsDeclP->Bool
isFunOrPatBind decl=isFunBind decl || isPatBind decl

-- | Return True if a declaration is a Class declaration.
isClassDecl :: HsDeclP ->Bool
isClassDecl (TiDecorate.Dec (HsClassDecl _ _ _ _ _)) = True
isClassDecl _ = False

-- | Return True if a declaration is a Class instance declaration.
isInstDecl :: HsDeclP -> Bool
isInstDecl (TiDecorate.Dec (HsInstDecl _ _ _ _ _)) = True
isInstDecl _ = False
        
-- | Return True if a function is a directly recursive function.
isDirectRecursiveDef::HsDeclP->Bool
isDirectRecursiveDef (TiDecorate.Dec (HsFunBind loc ms)) 
   = any isUsedInDef ms 
  where 
   isUsedInDef (HsMatch loc1 fun pats rhs ds)
     = findEntity (pNTtoPN fun) rhs
isDirectRecursiveDef _ = False

------------------------------------------------------------------------------------------------

-- | Add a qualifier to an identifier if it is not qualified.
qualifyPName::ModuleName  -- ^ The qualifier.
              ->PName     -- ^ The identifier.
              ->PName     -- ^ The result.
qualifyPName qual pn 
 = case pn of 
      PN (UnQual n) ty -> PN (Qual qual n ) ty
      _                -> pn

-- | Remove the qualifier from the given identifiers in the given syntax phrase.
rmQualifier::((MonadState (([PosToken], Bool), t1) m),Term t)
             =>[PName]  -- ^ The identifiers.
               ->t      -- ^ The syntax phrase.
               ->m t    -- ^ The result.
rmQualifier pns t 
  = applyTP (full_tdTP (adhocTP idTP rename )) t
   where 
     rename pnt@(PNT  pn@(PN (Qual modName  s) l) ty loc@(N (Just (SrcLoc fileName _ row col))))
       | elem pn pns
       = do do ((toks,_), others)<-get
               let toks' =replaceToks toks (row,col) (row,col) [mkToken Varid (row,col) s]
               put ((toks', modified), others)
               return (PNT (PN (UnQual s) l) ty loc)
     rename x = return  x

-- | Show a list of entities, the parameter f is a function that specifies how to format an entity.
showEntities::(Eq t, Term t)=>(t->String)->[t]->String
showEntities f [] = ""
showEntities f [pn] = f pn
showEntities f (pn:pns) =f pn ++ "," ++ showEntities f pns

-- | Show a PName in a format like: 'pn'(at row:r, col: c).
showPNwithLoc::PName->String
showPNwithLoc pn
  = let (SrcLoc _ _ r c)=srcLoc pn
    in  " '"++pNtoName pn++"'" ++"(at row:"++show r ++ ",col:" ++ show c ++")"


----------------------------------------------------------------------------------
-- | Default identifier in the PName format.
defaultPN::PName
defaultPN=PN (UnQual "unknown") (G (PlainModule "unknown") "--" (N Nothing)) :: PName

-- | Default identifier in the PNT format.
defaultPNT::PNT
defaultPNT=PNT defaultPN Value  (N Nothing) :: PNT 

-- | Default module name.
defaultModName::ModuleName
defaultModName = PlainModule "unknown"

-- | Default expression.
defaultExp::HsExpP
defaultExp=TiDecorate.Exp (HsId (HsVar defaultPNT))

-- | Default expression for untyped AST
defaultExpUnTyped::HsExpI PNT
defaultExpUnTyped = PosSyntax.Exp (HsId (HsVar defaultPNT))

-- | Default pattern.
defaultPat::HsPatP
defaultPat=TiDecorate.Pat (HsPId (HsVar defaultPNT))

------------------------------------------------------------------------------------

-- | From PNT to PName.
pNTtoPN :: PNT->PName
pNTtoPN (PNT pname _ _)=pname

-- | From PName to Name. This function ignores the qualifier.
pNtoName::PName->String
pNtoName (PN (UnQual i) orig)=i
pNtoName (PN (Qual modName i) orig)=i   

-- | From PNT to Name. This function ingnores the qualifier.
pNTtoName::PNT->String
pNTtoName=pNtoName.pNTtoPN
----------------------------------------------------------------------------------

class (Term t) => HasModName t where

    -- | Fetch the module name from an identifier.
    hasModName :: t->Maybe ModuleName

instance HasModName PNT  where

    hasModName (PNT (PN _ (G modName s1 loc)) _ _)=Just modName
    hasModName _ =Nothing   

instance HasModName PName where
  
    hasModName (PN _ (G modName s1 loc))=Just modName
    hasModName _ =Nothing

----------------------------------------------------------------------
-- | Compose a PNT form a String.
nameToPNT::String->PNT
nameToPNT id =(PNT (PN (UnQual id) (G (PlainModule "unknown") id
                 (N (Just loc0)))) Value (N (Just loc0)))

-- | Compose a PName from String.
nameToPN::String->PName
nameToPN id =(PN (UnQual id) (G (PlainModule "unknown") id (N (Just loc0))))

-- | Compose a PNT from a PName and the PName's name space Information
pNtoPNT::PName->IdTy PId->PNT
pNtoPNT pname ty =  PNT pname ty (N (Just loc0))

-- | If an expression consists of only one identifier then return this identifier in the PNT format,
--  otherwise return the default PNT.
expToPNT::HsExpP->PNT
expToPNT (TiDecorate.Exp (HsId (HsVar pnt)))=pnt 
expToPNT (TiDecorate.Exp (HsParen e))=expToPNT e 
expToPNT _ =defaultPNT

-- | If an expression consists of only one identifier then return this identifier in the PName format,
--   otherwise returns the default PName. 
expToPN::HsExpP->PName
expToPN =pNTtoPN.expToPNT

-- | Compose an expression from a String.
nameToExp ::String ->HsExpP
nameToExp name
    =TiDecorate.Exp (HsId (HsVar (PNT (PN (UnQual name) (UniqueNames.S loc0)) Value (N (Just loc0)))))

-- | Compose an expression from a pName.
pNtoExp::PName->HsExpP
pNtoExp pn =TiDecorate.Exp (HsId (HsVar (PNT pn  Value (N (Just loc0)))))

-- | If a pattern consists of only one identifier then return this identifier in the PNT format,
--  otherwise returns the default PNT. 
patToPNT::HsPatP->PNT
patToPNT (TiDecorate.Pat (HsPId (HsVar pnt)))= pnt
patToPNT (TiDecorate.Pat (HsPParen p))=patToPNT p
patToPNT _=defaultPNT

-- | If a pattern consists of only one identifier then returns this identifier in the PName format,
--   otherwise returns the default PName.
patToPN::HsPatP->PName
patToPN=pNTtoPN.patToPNT

-- | Compose a pattern from a String.
nameToPat::String->HsPatP
nameToPat name
    =TiDecorate.Pat (HsPId (HsVar (PNT (PN (UnQual name) (UniqueNames.S loc0)) Value (N (Just loc0)))))

-- | Compose a pattern from a pName.
pNtoPat :: PName -> HsPatP
pNtoPat pname
    =let loc=srcLoc pname
     in (TiDecorate.Pat (HsPId (HsVar (PNT pname Value (N (Just loc))))))
---------------------------------------------------------------------------


-- |Create a new name base on the old name. Suppose the old name is 'f', then 
--  the new name would be like 'f_i' where 'i' is an integer.
mkNewName::String      -- ^ The old name
          ->[String]   -- ^ The set of names which the new name cannot take
          ->Int        -- ^ The posfix value
          ->String     -- ^ The result
mkNewName oldName fds init
  =let newName=if init==0 then oldName
                          else oldName++"_"++ show init
   in if elem newName fds
        then mkNewName oldName fds (init+1)
        else newName 

-- | Return the identifier's defining location.
defineLoc::PNT->SrcLoc
defineLoc (PNT pname _ _) = srcLoc pname

-- | Return the identifier's source location.
useLoc::PNT->SrcLoc
useLoc (PNT pname _ (N (Just loc))) = loc
useLoc (PNT _ _ _ )                 = loc0

-- | Return True if the identifier is used in the RHS if a function\/pattern binding.
isUsedInRhs::(Term t)=>PNT->t->Bool
isUsedInRhs pnt t= useLoc pnt /= defineLoc pnt  && not (notInLhs pnt t)
  where
    notInLhs pnt
     = (fromMaybe False).(applyTU (once_tdTU (failTU `adhocTU` inMatch
                                                     `adhocTU` inDecl)))
     where
      inMatch ((HsMatch loc1 name pats rhs ds)::HsMatchP)
         | isJust (find (sameOccurrence pnt) [name]) = Just True
      inMatch _ =Nothing

      inDecl ((TiDecorate.Dec (HsTypeSig loc is c tp))::HsDeclP)
        |isJust (find (sameOccurrence pnt) is)   = Just True
      inDecl _ =Nothing    

-- | Return True is the identifier is unqualifiedly used in the given syntax phrase.
usedWithoutQual::(Term t)=>String->t->Bool
usedWithoutQual name t
   =(fromMaybe False) (applyTU (once_tdTU (failTU `adhocTU` worker)) t)
      where
         worker (pnt::PNT)
           |pNTtoName pnt ==name && isUsedInRhs pnt t && not (isQualifiedPN (pNTtoPN pnt)) 
          = Just True
         worker _ =Nothing

-- |Find the identifier(in PNT format) whose start position is (row,col) in the
-- file specified by the fileName, and returns defaultPNT is such an identifier does not exist.

locToPNT::(Term t)=>String      -- ^ The file name 
                    ->(Int,Int) -- ^ The row and column number               
                    ->t         -- ^ The syntax phrase
                    ->PNT       -- ^ The result
locToPNT  fileName (row, col) 
  =(fromMaybe defaultPNT). applyTU (once_buTU (failTU `adhocTU` worker))
     where 
        worker pnt@(PNT pname ty (N (Just (SrcLoc fileName1 _ row1 col1))))
           |fileName1==fileName && (row1,col1) == (row,col) =Just pnt
        worker _ =Nothing 



-- | The same as locToPNT, except that it returns the identifier in the PName format.
locToPN::(Term t)=>String->(Int,Int)->t->PName
locToPN fileName pos = pNTtoPN.(locToPNT fileName pos)



-- | Given the syntax phrase (and the token stream), find the largest-leftmost expression contained in the
--  region specified by the start and end position. If no expression can be found, then return the defaultExp.
locToExp::(Term t) => RefacTITypeSyn.SimpPos   -- ^ The start position.
                  -> RefacTITypeSyn.SimpPos    -- ^ The end position.
                  -> [PosToken]         -- ^ The token stream which should at least contain the tokens for t.
                  -> t                  -- ^ The syntax phrase.
                  -> HsExpP             -- ^ The result.
locToExp beginPos endPos toks t
  = fromMaybe defaultExp $ applyTU (once_tdTU (failTU `adhocTU` exp)) t
     where
       {- exp (e@(Exp (HsDo stmts))::HsExpP)
         | filter inScope (map (getStartEndLoc toks) (getStmtList stmts))/=[]
         = do let atoms = filter (\atom->inScope (getStartEndLoc toks atom)) (getStmtList stmts)
                  atoms'= reverse (dropWhile (not.isQualifierOrLastAtom) (reverse atoms))
              if atoms'==[] 
                  then fail "Expession not selected"
                  else do stmts' <-atoms2Stmt atoms'  
                          Just (Exp (HsDo stmts')) -}
        exp (e::HsExpP)
         |inScope e = Just e
        exp _ =Nothing                     
             
        inScope e 
          = let (startLoc, endLoc) 
                 = if expToPNT e /= defaultPNT 
                    then let (SrcLoc _ _ row col) = useLoc (expToPNT e)
                         in ((row,col), (row,col))
                    else getStartEndLoc toks e
            in (startLoc>=beginPos) && (startLoc<= endPos) && (endLoc>= beginPos) && endLoc<=endPos   

        isQualifierOrLastAtom (HsQualifierAtom e) = True
        isQualifierOrLastAtom (HsLastAtom e)      = True
        isQualifierOrLastAtom _ = False 
 
        atoms2Stmt [HsQualifierAtom e]          = return (HsLast e)
        atoms2Stmt [HsLastAtom e]               = return (HsLast e)
        atoms2Stmt (HsGeneratorAtom s p e : ss) = HsGenerator s p e # atoms2Stmt ss
        atoms2Stmt (HsLetStmtAtom ds : ss)      = HsLetStmt ds # atoms2Stmt ss
        atoms2Stmt (HsQualifierAtom e : ss)     = HsQualifier e # atoms2Stmt ss
        atoms2Stmt _ = fail "last statement in a 'do' expression must be an expression"
  
---------------------------------------------------------------------------------------
-- | Collect the identifiers (in PName format) in a given syntax phrase.     
hsPNs::(Term t)=> t->[PName]
hsPNs=(nub.ghead "hsPNs").applyTU (full_tdTU (constTU [] `adhocTU` inPnt)) 
  where 
     inPnt (PNT pname ty loc) = return [pname]

-- | Collect the identifiers (in PNT format) in a given syntax phrase.
hsPNTs ::(Term t)=>t->[PNT]
hsPNTs =(nub.ghead "hsPNTs").applyTU (full_tdTU (constTU [] `adhocTU` inPnt))
   where
     inPnt pnt@(PNT _  _ _) = return [pnt]


-- |Find those declarations(function\/pattern binding and type signature) which define the specified PNames.
--incTypeSig indicates whether the corresponding type signature will be included.
definingDecls::[PName]         -- ^ The specified identifiers.
            ->[HsDeclP]        -- ^ A collection of declarations.
            ->Bool             -- ^ True means to include the type signature.
            ->Bool             -- ^ True means to look at the local declarations as well. 
            ->[HsDeclP]        -- ^ The result.
definingDecls pns ds incTypeSig recursive=concatMap defines ds  
  where
   defines decl
     =if recursive
        then ghead "defines" $ applyTU (stop_tdTU (failTU `adhocTU` inDecl)) decl
        else defines' decl
     where
      inDecl (d::HsDeclP)
        |defines' d /=[] =return $ defines' d
      inDecl _=mzero 

      defines' decl@(TiDecorate.Dec (HsFunBind _ ((HsMatch _ (PNT pname _ _) _ _ _):ms))) 
        |isJust (find (==pname) pns) = [decl]
      defines' decl@(TiDecorate.Dec (HsPatBind loc p rhs ds))    ---CONSIDER AGAIN----
        |(hsPNs p) `intersect` pns /=[] = [decl]
      defines' decl@(TiDecorate.Dec (HsTypeSig loc is c tp))     --handle cases like  a,b::Int 
        |(map pNTtoPN is) `intersect` pns /=[]
        =if incTypeSig 
           then [(TiDecorate.Dec (HsTypeSig loc (filter (\x->isJust (find (==pNTtoPN x) pns)) is) c tp))]
           else []
      defines' decl@(TiDecorate.Dec (HsDataDecl loc c tp cons i))
       = if checkCons cons == True then [decl]
                                   else []
                                     
             where
               checkCons [] = False
               checkCons ((HsConDecl loc i c (PNT pname _ _) t):ms)
                 | isJust (find (==pname) pns) = True
                 | otherwise = checkCons ms
      defines' _ =[]   

-- | Return True if the  function\/pattern binding defines the specified identifier.
defines::PName->HsDeclP->Bool
defines pn decl@(TiDecorate.Dec (HsFunBind loc ((HsMatch loc1 (PNT pname ty loc2) pats rhs ds):ms))) 
 = pname == pn
defines pn decl@(TiDecorate.Dec (HsPatBind loc p rhs ds)) = elem pn (hsPNs p)
defines _ _= False


-- | Return True if the declaration defines the type signature of the specified identifier.
definesTypeSig :: PName -> HsDeclP -> Bool
definesTypeSig pn (TiDecorate.Dec (HsTypeSig loc is c tp))=elem pn (map pNTtoPN is)  
definesTypeSig _  _ =False


-- | Return True if the declaration defines the type signature of the specified identifier.
isTypeSigOf :: PNT -> HsDeclP -> Bool
isTypeSigOf pnt (TiDecorate.Dec (HsTypeSig loc is c tp))= elem pnt is  
isTypeSigOf _  _ =False


-- | Return the list of identifiers (in PName format) defined by a function\/pattern binding.
definedPNs::HsDeclP->[PName]
definedPNs (TiDecorate.Dec (HsFunBind _ ((HsMatch _ (PNT pname _ _) _ _ _):_))) =[pname]
definedPNs (TiDecorate.Dec (HsPatBind _ p _ _)) =hsPNs p
definedPNs (TiDecorate.Dec (HsDataDecl _ _ _ cons _) )
   = getCons cons 
       where
         getCons [] = []
         getCons ((HsConDecl _ _ _ (PNT pname _ _) _):ms)
           = pname : (getCons ms)
         getCons ((HsRecDecl _ _ _ (PNT pname _ _) _):ms)
           = pname : (getCons ms)  
         getCons _ = []
definedPNs _=[] 


-- |Return True if the given syntax phrase contains any free variables.
hasFreeVars::(Term t)=>t->Bool
hasFreeVars t = fromMaybe False (do (f,_)<-hsFreeAndDeclaredPNs t
                                    if f/=[] then Just True
                                             else Nothing) 

{- Remove source location information in the syntax tree. that is to replace all
   source locations by default location: loc0 -}       
-- | Remove source location information in the syntax tree.
rmLocs :: (Term t)=> t->t 
rmLocs t =runIdentity (applyTP (full_tdTP (idTP `adhocTP` exp
                                                `adhocTP` pnt
                                                `adhocTP` alt
                                                `adhocTP` lit)) t) 
   where 
         exp ((TiDecorate.Exp (HsNegApp loc e)) ::HsExpP)=return (TiDecorate.Exp (HsNegApp loc0 e))
         exp (TiDecorate.Exp (HsExpTypeSig loc e c t))=return (TiDecorate.Exp (HsExpTypeSig loc0 e c t))
         exp x=return x 

         alt ((HsAlt loc p e ds)::HsAltP)=return (HsAlt loc0 p e ds)

         lit (HsInt int) = return (HsInt int)
         lit (HsFrac rat)= return (HsFrac rat)

         pnt (PNT pname ty _)= return (PNT pname ty (N (Just loc0)))

-- | Change the absolute define locations of local variables to relative ones,
--   so that equality between expressions can be compared via alpha-renaming.

toRelativeLocs::(Term t)=>t->t
toRelativeLocs e = runIdentity (applyTP (full_tdTP (idTP `adhocTP` inLoc)) e)
  where
    inLoc (SrcLoc f c row col)
      | elem (row,col) defLocs
          = let index=fromJust (elemIndex (row,col) defLocs) + 1 
            in return (SrcLoc f index index index)
    inLoc loc = return loc

    defLocs= ((nub.ghead "toRelativeLoc").applyTU (full_tdTU (constTU [] 
                                                      `adhocTU` inPnt ))) e
        where
         inPnt pnt@(PNT pn ty loc)
            |defineLoc pnt == useLoc pnt= return [(\(SrcLoc _ _ r c)->(r,c)) (srcLoc pn)]
         inPnt _ = return []
         
    
------------------------------------------------------------------------------------------ 
-- | Replace the name (and qualifier if specified) by a new name (and qualifier) in a PName.
--   The function does not modify the token stream.
replaceNameInPN::Maybe ModuleName    -- ^ The new qualifier
                 ->PName             -- ^ The old PName
                 ->String            -- ^ The new name 
                 ->PName             -- ^ The result 
replaceNameInPN qualifier (PN (UnQual s)(UniqueNames.S loc))  newName
  = if isJust qualifier then (PN (Qual (fromJust qualifier) newName) (UniqueNames.S loc))
                        else (PN (UnQual newName) (UniqueNames.S loc)) 
replaceNameInPN qualifier (PN (Qual modName  s)(UniqueNames.S loc))  newName
  = if isJust qualifier  then (PN (Qual (fromJust qualifier) newName)(UniqueNames.S loc))
                         else (PN (Qual modName newName) (UniqueNames.S loc))
replaceNameInPN qualifier (PN (UnQual s) (G modName s1 loc))  newName
  = if isJust qualifier then (PN (Qual (fromJust qualifier)  newName) (G modName newName loc))
                        else (PN (UnQual newName) (G modName newName loc)) 
replaceNameInPN qualifier (PN (Qual modName s) (G modName1 s1 loc))  newName
  =if isJust qualifier then (PN (Qual (fromJust qualifier) newName) (G modName1 newName loc)) 
                       else (PN (Qual modName newName) (G modName1 newName loc))

-- | Rename each occurrences of the identifier in the given syntax phrase with the new name.
--   If the Bool parameter is True, then modify both the AST and the token stream, otherwise only modify the AST.

{-
renamePN::(Term t)
           =>PName               -- ^ The identifier to be renamed.
             ->Maybe ModuleName  -- ^ The qualifier
             ->String            -- ^ The new name 
             ->Bool              -- ^ True means modifying the token stream as well.
             ->t                 -- ^ The syntax phrase
             ->m t  
-}

renamePN::((MonadState (([PosToken], Bool), t1) m),Term t)
           =>PName               -- ^ The identifier to be renamed.
             ->Maybe ModuleName  -- ^ The qualifier
             ->String            -- ^ The new name 
             ->Bool              -- ^ True means modifying the token stream as well.
             ->t                 -- ^ The syntax phrase
             ->m t  

renamePN oldPN qualifier newName updateToks t
  = applyTP (full_tdTP (adhocTP idTP rename)) t
  where
    rename  pnt@(PNT pn ty (N (Just (SrcLoc fileName c  row col))))
     | (pn ==oldPN) && (srcLoc oldPN == srcLoc pn)
     = do if updateToks  
           then  do ((toks,_),others)<-get                           
                    let toks'=replaceToks toks (row,col) (row,col)
                              [mkToken Varid  (row,col) ((render.ppi) (replaceName pn  newName))]
                    put ((toks', modified),others)
                    return (PNT (replaceName pn newName) ty (N (Just (SrcLoc fileName c  row col))))
           else return (PNT (replaceName pn newName) ty (N (Just (SrcLoc fileName c  row col))))
      where 
        replaceName = if isJust qualifier && canBeQualified pnt t 
                        then replaceNameInPN qualifier
                        else replaceNameInPN Nothing       
    rename x = return x 
  
-- | Return True if the identifier can become qualified.
canBeQualified::(Term t)=>PNT->t->Bool
canBeQualified pnt t
  = isTopLevelPNT pnt && isUsedInRhs pnt t && not (findPntInImp pnt t) 
  where 
    findPntInImp pnt 
      = (fromMaybe False).(applyTU (once_tdTU (failTU `adhocTU` inImp)))
      where 
       inImp ((HsImportDecl loc modName qual  as h)::HsImportDeclP)
        |findEntity pnt h = Just True
       inImp _ = Nothing
  
 
-- | Return True if the identifier(in PNT format) occurs in the given syntax phrase.
findPNT::(Term t)=>PNT->t->Bool  
findPNT pnt 
  = (fromMaybe False).(applyTU (once_tdTU (failTU `adhocTU` worker)))
  where
    worker (pnt1::PNT)
      | sameOccurrence pnt pnt1 =Just True
    worker _ =Nothing  

-- | Return True if the identifier (in PName format) occurs in the given syntax phrase.
findPN::(Term t)=>PName->t->Bool
findPN pn 
  =(fromMaybe False).(applyTU (once_tdTU (failTU `adhocTU` worker)))
     where 
        worker (pn1::PName)
           |pn == pn1 && srcLoc pn == srcLoc pn1 = Just True 
        worker _ =Nothing 

-- | Return True if any of the specified PNames ocuur in the given syntax phrase.
findPNs::(Term t)=>[PName]->t->Bool 
findPNs pns 
   =(fromMaybe False).(applyTU (once_tdTU (failTU `adhocTU` worker)))
     where 
        worker (pn1::PName)
           |elem pn1 pns = Just True
        worker _ =Nothing  



----------------------------------------------------------------------------------------
-- | Check whether the specified identifier is declared in the given syntax phrase t,
-- if so, rename the identifier by creating a new name automatically. If the Bool parameter 
-- is True, the token stream will be modified, otherwise only the AST is modified. 

{-
autoRenameLocalVar::(MonadPlus m, Term t)
                    =>Bool         -- ^ True means modfiying the token stream as well.  
                     ->PName       -- ^ The identifier.
                     ->t           -- ^ The syntax phrase.
                     -> m t        -- ^ The result.
-}
autoRenameLocalVar::(MonadPlus m, (MonadState (([PosToken], Bool), (Int,Int)) m), Term t)
                    =>Bool         -- ^ True means modfiying the token stream as well.  
                     ->PName       -- ^ The identifier.
                     ->t           -- ^ The syntax phrase.
                     -> m t        -- ^ The result.


autoRenameLocalVar updateToks pn 
  =applyTP (once_buTP (failTP `adhocTP` renameInMatch 
                              `adhocTP` renameInPat
                              `adhocTP` renameInExp
                              `adhocTP` renameInAlt
                              `adhocTP` renameInStmts))  
      where 
         renameInMatch (match::HsMatchP)
           |isDeclaredIn pn match=worker match
         renameInMatch _ =mzero
     
         renameInPat (pat::HsDeclP)
          |isDeclaredIn pn pat=worker pat                 
         renameInPat _ =mzero
     
         renameInExp (exp::HsExpP)
          |isDeclaredIn pn exp=worker exp                 
         renameInExp _ =mzero
 
         renameInAlt (alt::HsAltP)
          |isDeclaredIn pn alt=worker alt                 
         renameInAlt _ =mzero
       
         renameInStmts (stmt::HsStmtP)
          |isDeclaredIn pn stmt=worker stmt
         renameInStmts _=mzero
         
         worker t =do (f,d)<-hsFDNamesFromInside t
                      ds<-hsVisibleNames pn (hsDecls t)
                      let newName=mkNewName (pNtoName pn) (nub (f `union` d `union` ds)) 1
                      if updateToks
                        then renamePN pn Nothing newName True t 
                        else renamePN pn Nothing newName False t     

-------------------------------------------------------------------------------------
-- | Add a guard expression to the RHS of a function\/pattern definition. If a guard already
--   exists in the RHS, the new guard will be added to the beginning of the existing one.
addGuardsToRhs::(MonadState (([PosToken], Bool), (Int,Int)) m)
                => RhsP     -- ^ The RHS of the declaration.
                -> HsExpP   -- ^ The guard expression to be added.
                -> m RhsP     -- ^ The result.
addGuardsToRhs (HsBody e) guardExp 
  = do ((toks,_), (v1,v2)) <-get
       let (startPos', _) = startEndLoc toks e
           (toks1,toks2) = break (\t->tokenPos t==startPos') toks
           reversedToks1BeforeEqOrArrow = dropWhile (\t->not (isEqual t || isArrow t)) (reverse toks1) 
           eqOrArrowTok = ghead "addGuardsToRhs"  reversedToks1BeforeEqOrArrow
           startPos = tokenPos eqOrArrowTok 
           offset = lengthOfLastLine (reverse (gtail "addGuardsToRhs" reversedToks1BeforeEqOrArrow))
           newCon = "|"++(render.ppi) guardExp ++ "\n" ++ replicate offset ' '++ tokenCon eqOrArrowTok
           newToks = tokenise (Pos 0 v1 1) 0  False newCon
           toks' = replaceToks toks startPos startPos newToks
       put ((toks',modified), ((tokenRow (glast "addFormalParams" newToks) -10), v2))
   --    (guardExp',_) <- addLocInfo (guardExp, newToks)    
       return $ HsGuard [(loc0, guardExp, e)]

addGuardsToRhs (HsGuard gs) guardExp
  = do newGuards <- mapM (addGuard guardExp) gs
       return (HsGuard newGuards)
   where 
   addGuard guardExp (loc, e1, e2)
     = do (e', _)<-updateToks e1 (TiDecorate.Exp (HsInfixApp guardExp (HsVar (nameToPNT "&&")) e1)) prettyprint
          return (loc, e', e2)


------------------------------------------------------------------------------------------------------
{-
addParamsToDecls::(MonadPlus m) 
               => [HsDeclP]   -- ^ A declaration list where the function is defined and\/or used.
                  ->PName     -- ^ The function name.
                  ->[PName]   -- ^ The parameters to be added.
                  ->Bool      -- ^ Modify the token stream or not.
                  ->m [HsDeclP] -- ^ The result. 
-}

addParamsToDecls::(MonadPlus m, (MonadState (([PosToken], Bool), (Int,Int)) m))
               => [HsDeclP]   -- ^ A declaration list where the function is defined and\/or used.
                  ->PName     -- ^ The function name.
                  ->[PName]   -- ^ The parameters to be added.
                  ->Bool      -- ^ Modify the token stream or not.
                  ->m [HsDeclP] -- ^ The result.
 
addParamsToDecls decls pn paramPNames modifyToks
   = if (paramPNames/=[])
        then mapM addParamToDecl decls
        else return decls 
  where 
   addParamToDecl (TiDecorate.Dec (HsFunBind loc matches@((HsMatch _ fun pats rhs ds):ms)))
    | pNTtoPN fun == pn
    = do matches'<-mapM addParamtoMatch matches 
         return (TiDecorate.Dec (HsFunBind loc matches'))
      where 
       addParamtoMatch (HsMatch loc  fun  pats rhs  decls) 
        = do rhs'<-addActualParamsToRhs pn paramPNames rhs 
             let pats' = map pNtoPat paramPNames 
             pats'' <- if modifyToks then do (p, _)<-addFormalParams fun pats'
                                             return p
                                     else return pats' 
             return (HsMatch loc  fun  (pats'++pats)  rhs' decls)

   addParamToDecl (TiDecorate.Dec (HsPatBind loc p rhs ds))
     |patToPN p == pn 
       = do rhs'<-addActualParamsToRhs pn paramPNames rhs
            let pats' = map pNtoPat paramPNames 
            pats'' <- if modifyToks  then do (p, _) <-addFormalParams p pats'
                                             return p
                                     else return pats'                        
            return (TiDecorate.Dec (HsFunBind loc [HsMatch loc (patToPNT p) pats' rhs ds]))
   addParamToDecl x=return x 
 
   addActualParamsToRhs pn paramPNames
    = applyTP (stop_tdTP (failTP `adhocTP` worker))  
     where                   
       worker exp@(TiDecorate.Exp (HsId (HsVar (PNT pname ty loc))))
        | pname==pn
         = do let newExp=TiDecorate.Exp (HsParen (foldl addParamToExp exp (map pNtoExp paramPNames)))
              if modifyToks then do (newExp', _) <- updateToks exp newExp prettyprint
                                    return newExp' 
                            else return newExp
       worker x =mzero 

       addParamToExp  exp param=(TiDecorate.Exp (HsApp exp param))

 
-------------------------------------------------------------------

-- | Remove the first n parameters of a given identifier in an expression.
rmParams:: (MonadPlus m,MonadState (([PosToken], Bool), (Int,Int)) m)=>
             PNT          -- ^ The identifier whose parameters are to be removed.
             ->Int        -- ^ Number of parameters to be removed.
             ->HsExpP     -- ^ The original expression.
             ->m HsExpP   -- ^ The result expression.
rmParams pnt n exp 
  = if n==0 then return exp
            else do exp'<-rmOneParam pnt exp
                    rmParams pnt (n-1) exp' 
   where 
         rmOneParam pnt= applyTP (stop_tdTP (failTP `adhocTP` inExp))
       
         inExp (exp@(TiDecorate.Exp (HsParen (TiDecorate.Exp (HsApp e1 e2))))::HsExpP)
          ---dfd
           |sameOccurrence (expToPNT e1) pnt 
            =do updateExp exp e1     
         inExp exp@(TiDecorate.Exp (HsApp e1 e2))
           | sameOccurrence (expToPNT e1) pnt
            =do updateExp exp e1
         inExp  _=mzero

         updateExp exp e1 
           = do ((toks,_),others)<-get     --handle the case like '(fun x) => fun "
                let (startPos,endPos)=getStartEndLoc toks exp
                    toks'=replaceToks toks startPos endPos $ getToks (getStartEndLoc toks e1) toks
                put ((toks',modified),others)
                return e1  
             
-------------------------------------------------------------------------------------------------------


{-A simple function binding satisfies : 1. all parameters are variables
                                        2. only one match(equation)
                                        3. The rhs of the match is not in guard style.
  that is:
   HsFunBind SrcLoc ((HsMatch SrcLoc i [var] (HsBody e) ds):[]) ds

  If a function binding is not a simple function binding, then convert it into a simple binding 
  using Case or IfThenElse expressions like this:
    case1: there are multi matches => case expression
    case2: there is only one match, however the parameters are not simple variables =>case expression.
    case3: there is only one match and the parameters are all simple variables, however there is a guard
           in Rhs => If then else

  In case of pattern binding: if there is guard in its Rhs, then convert it into IfThenElse style. -}

                              
-- | If a function\/pattern binding then convert it into a simple binding using case and\/or if-then-else expressions.     
-- A simple function\/pattern binding should satisfy: a) all the paraneters are simple variables; b). only has one equation; 
-- c). the RHS does not have guards. This function DOES NOT modify the token stream not AST.
simplifyDecl::(Monad m)=>HsDeclP->m HsDeclP
simplifyDecl decl
      |isFunBind decl =if (multiMatches decl) || (singleMatchWithComplexParams decl)
                           then matchesToCase decl
                           else return (guardToIfThenElse decl)
      |isPatBind decl=return (guardToIfThenElse  decl)

      |otherwise      = return decl
   where

      multiMatches (TiDecorate.Dec (HsFunBind loc matches))=length matches>1
      multiMatches _ = False 

      singleMatchWithComplexParams (TiDecorate.Dec (HsFunBind loc matches@((HsMatch loc1 pnt pats rhs ds):ms)))
            =length matches==1 && any (==defaultPN) (map patToPN pats)
      singleMatchWithComplexParams _ =False

      --convert a multi-match function declaration into a single-match declration using case expression.
      matchesToCase decl@(TiDecorate.Dec (HsFunBind loc matches@((HsMatch loc1 pnt pats rhs ds):ms)))
        =do params<-mkNewParamPNames (length pats)
            exp<-pNamesToExp params
            return (TiDecorate.Dec (HsFunBind loc [(HsMatch loc1 pnt (map pNtoPat params)
                      (HsBody (TiDecorate.Exp (HsCase exp (map matchToAlt matches)))) (Decs [] ([], [])))]))

      --make n new parameters like [x_0,x_1, ...,x_n]
      mkNewParamPNames n=mkNewParamPNames' n []
              where mkNewParamPNames' n pNames
                         =if n==0 then return pNames
                                     else do let pn'= PN (UnQual  ("x_"++show (n-1))) (UniqueNames.S loc0)
                                             mkNewParamPNames' (n-1) (pn':pNames)
                                        
      matchToAlt ((HsMatch loc1 pnt pats rhs ds)::HsMatchP)=HsAlt loc0 (listToTuple pats) rhs ds
        where
         listToTuple pats=if (length pats)==1 then ghead "listToTuple" pats   --no problem with head
                                              else (TiDecorate.Pat (HsPTuple loc0 pats))

      pNamesToExp pns@(p:ps)=if ps==[] then return $ pNtoExp p
                                        else  do let exp'=map pNtoExp pns
                                                 return (TiDecorate.Exp (HsTuple exp')) 
     
      guardToIfThenElse decl= case decl of
          (TiDecorate.Dec (HsPatBind loc p g@(HsGuard gs) ds))->(TiDecorate.Dec (HsPatBind loc p (rmGuard g) ds))
          (TiDecorate.Dec (HsFunBind loc ((HsMatch loc1 pnt pats  g@(HsGuard gs) ds):[]))) ->
                            (TiDecorate.Dec (HsFunBind loc ((HsMatch loc1 pnt pats (rmGuard g) ds):[])))
          _ ->decl
           
          where
           rmGuard ((HsGuard gs)::RhsP)
             = let (_,e1,e2)=glast "guardToIfThenElse" gs
               in  if ((pNtoName.expToPN) e1)=="otherwise" 
                   then  HsBody (foldl mkIfThenElse e2 (tail(reverse gs)))
                   else  HsBody (foldl mkIfThenElse defaultElse (reverse gs)) 
           
           mkIfThenElse e (_,e1, e2)=(TiDecorate.Exp (HsIf e1 e2 e)) 

           defaultElse=(TiDecorate.Exp (HsApp (TiDecorate.Exp (HsId (HsVar (PNT (PN (UnQual "error") (G (PlainModule "Prelude") "error" 
                        (N (Just loc0)))) Value (N (Just loc0)))))) (TiDecorate.Exp (HsLit loc0 (HsString "UnMatched Pattern")))))
            

-----------------------------------------------------------------------------------------
-- | Collect those data constructors that occur in the given syntax phrase, say t. In the result, 
--   the first list contains the data constructors that are declared in other modules, and the second
--   list contains the data constructors that are declared in the current module.
hsDataConstrs::Term t=>ModuleName              -- ^ The name of the module which 't' belongs to.
                     -> t                      -- ^ The given syntax phrase.
                     ->([PName],[PName])       -- ^ The result.
hsDataConstrs modName  
  = ghead "hsDataConstrs". (applyTU (stop_tdTU (failTU `adhocTU` pnt)))  
  where
    pnt (PNT pname (ConstrOf _  _) _)
      = if hasModName pname==Just modName 
          then return ([],[pname])
          else return ([pname],[])
    pnt _ = mzero


-- | Collect those type constructors and class names that occur in the given syntax phrase, say t.
--   In the result, the first list contains the type constructor\/classes which are
--   declared in other modules, and the second list contains those type constructor\/classes
--  that are declared in the current module.

hsTypeConstrsAndClasses::Term t=>ModuleName                  -- ^ The name of the module which 't' belongs to.
                               -> t                          -- ^ The given syntax phrase.
                               -> ([PName],[PName])          -- ^ The result.
hsTypeConstrsAndClasses modName
  = ghead "hsTypeConstrAndClasses".(applyTU (stop_tdTU (failTU `adhocTU` pnt))) 
  where 
    pnt (PNT (PN i (G  modName1 id loc)) (Type _) _)
      = if modName == modName1
                     then return ([],[(PN i (G  modName id loc))])
                     else return ([(PN i (G  modName id loc))], [])
    pnt (PNT pname (TypedIds.Class _ _) _)=if hasModName pname==Just modName 
                                 then return ([],[pname])
                                 else return ([pname],[])
    pnt _ =mzero


-- |Collect those type variables that are declared in a given syntax phrase t.
-- In the returned result, the first list is always be empty.
hsTypeVbls::(Term t) => t -> ([PName],[PName])
hsTypeVbls =ghead "hsTypeVbls".(applyTU (stop_tdTU (failTU `adhocTU` pnt))) 
  where 
    pnt (PNT (PN i (UniqueNames.S loc)) (Type _) _) = return ([], [(PN i (UniqueNames.S loc))])
    pnt _ =mzero


-- |Collect the class instances of the spcified class from the given syntax phrase. In the result,
-- the first list contains those class instances which are declared in other modules, 
-- and the second list contains those class instances that are declared in the current module.
hsClassMembers::Term t => String               -- ^ The class name.
                        ->ModuleName           -- ^ The module name.
                        ->t                    -- ^ The syntax phrase.
                        ->([PName],[PName])    -- ^ The result.
hsClassMembers className modName 
    = ghead "hsClassMembers". (applyTU (stop_tdTU (failTU `adhocTU` pnt))) 
         where
            pnt(PNT pname (MethodOf i _ _) _) -- Claus
                | pNtoId i==className
                  = if hasModName pname == Just modName 
                      then return ([],[pname])
                      else return ([pname],[])
            pnt _ = mzero   
            
            pNtoId :: PN (HsName.Id) ->String
            pNtoId (PN i orig)=i

------------------------------------------------------------------------------------------
-- | Collect the free and declared variables (in the PName format) in a given syntax phrase t.
-- In the result, the first list contains the free variables, and the second list contains the declared variables.
hsFreeAndDeclaredPNs:: (Term t, MonadPlus m)=> t-> m ([PName],[PName])
hsFreeAndDeclaredPNs t=do (f,d)<-hsFreeAndDeclared' t
                          return (nub f, nub d)
   where 
          hsFreeAndDeclared'=applyTU (stop_tdTU (failTU  `adhocTU` exp
                                                         `adhocTU` pat
                                                         `adhocTU` match
                                                         `adhocTU` patBind
                                                         `adhocTU` alt
                                                         `adhocTU` decls
                                                         `adhocTU` stmts
                                                         `adhocTU` recDecl))  
                          
          exp (TiDecorate.Exp (HsId (HsVar (PNT pn _ _))))=return ([pn],[])
          exp (TiDecorate.Exp (HsId (HsCon (PNT pn _ _))))=return ([pn],[])
          exp (TiDecorate.Exp (HsInfixApp e1 (HsVar (PNT pn _ _)) e2))
              =addFree pn (hsFreeAndDeclaredPNs [e1,e2])
          exp (TiDecorate.Exp (HsLambda pats body))
              = do (pf,pd) <-hsFreeAndDeclaredPNs pats
                   (bf,_) <-hsFreeAndDeclaredPNs body
                   return ((bf `union` pf) \\ pd, [])
          exp (TiDecorate.Exp (HsLet decls exp))
              = do (df,dd)<- hsFreeAndDeclaredPNs decls
                   (ef,_)<- hsFreeAndDeclaredPNs exp 
                   return ((df `union` (ef \\ dd)),[])
          exp (TiDecorate.Exp (HsRecConstr _  (PNT pn _ _) e))
               =addFree  pn  (hsFreeAndDeclaredPNs e)   --Need Testing
          exp (TiDecorate.Exp (HsAsPat (PNT pn _ _) e))
              =addFree  pn  (hsFreeAndDeclaredPNs e)  
          exp _ = mzero

          
          pat (TiDecorate.Pat (HsPId (HsVar (PNT pn _ _))))=return ([],[pn])
          pat (TiDecorate.Pat (HsPInfixApp p1 (PNT pn _ _) p2))=addFree pn (hsFreeAndDeclaredPNs [p1,p2])
          pat (TiDecorate.Pat (HsPApp (PNT pn _ _) pats))=addFree pn (hsFreeAndDeclaredPNs pats)
          pat (TiDecorate.Pat (HsPRec (PNT pn _ _) fields))=addFree pn (hsFreeAndDeclaredPNs fields)
          pat _ =mzero
                               

          match ((HsMatch _ (PNT fun _ _)  pats rhs  decls)::HsMatchP)
            = do (pf,pd) <- hsFreeAndDeclaredPNs pats
                 (rf,rd) <- hsFreeAndDeclaredPNs rhs
                 (df,dd) <- hsFreeAndDeclaredPNs decls
                 return ((pf `union` ((rf `union` df) \\ (dd `union` pd `union` [fun]))),[fun])

         -------Added by Huiqing Li-------------------------------------------------------------------

          patBind ((TiDecorate.Dec (HsPatBind _ pat (HsBody rhs) decls))::HsDeclP)
             =do (pf,pd) <- hsFreeAndDeclaredPNs pat
                 (rf,rd) <- hsFreeAndDeclaredPNs rhs
                 (df,dd) <- hsFreeAndDeclaredPNs decls
                 return (pf `union` ((rf `union` df) \\(dd `union` pd)),pd)
          patBind _=mzero
         ------------------------------------------------------------------------------------------- 

          alt ((HsAlt _ pat exp decls)::(HsAlt (HsExpP) (HsPatP) HsDeclsP))
             = do (pf,pd) <- hsFreeAndDeclaredPNs pat
                  (ef,ed) <- hsFreeAndDeclaredPNs exp
                  (df,dd) <- hsFreeAndDeclaredPNs decls
                  return (pf `union` (((ef \\ dd) `union` df) \\ pd),[])


          decls (ds :: [HsDeclP])
             =do (f,d) <-hsFreeAndDeclaredList ds
                 return (f\\d,d)
          
          stmts ((HsGenerator _ pat exp stmts) :: HsStmt (HsExpP) (HsPatP) HsDeclsP) -- Claus
             =do (pf,pd) <-hsFreeAndDeclaredPNs pat
                 (ef,ed) <-hsFreeAndDeclaredPNs exp
                 (sf,sd) <-hsFreeAndDeclaredPNs stmts
                 return (pf `union` ef `union` (sf\\pd),[]) -- pd) -- Check this 

          stmts ((HsLetStmt decls stmts) :: HsStmt (HsExpP) (HsPatP) HsDeclsP)
             =do (df,dd) <-hsFreeAndDeclaredPNs decls
                 (sf,sd) <-hsFreeAndDeclaredPNs stmts
                 return (df `union` (sf \\dd),[])
          stmts _ =mzero

          recDecl ((HsRecDecl _ _ _ _ is) :: HsConDeclI PNT (HsTypeI PNT) [HsTypeI PNT])
                =do let d=map pNTtoPN $ concatMap fst is
                    return ([],d)
          recDecl _ =mzero
            
       
          addFree free mfd=do (f,d)<-mfd
                              return ([free] `union` f, d)

          hsFreeAndDeclaredList l=do fds<-mapM hsFreeAndDeclaredPNs l
                                     return (foldr union [] (map fst fds),
                                             foldr union [] (map snd fds))

-- |The same as `hsFreeAndDeclaredPNs` except that the returned variables are in the String format.           
hsFreeAndDeclaredNames::(Term t, MonadPlus m)=> t->m([String],[String])
hsFreeAndDeclaredNames t =do (f1,d1)<-hsFreeAndDeclaredPNs t
                             return ((nub.map pNtoName) f1, (nub.map pNtoName) d1)

-----------------------------------------------------------------------------------------
{- |`hsFDsFromInside` is different from `hsFreeAndDeclaredPNs` in that: given an syntax phrase t,
    `hsFDsFromInside` returns not only the declared variables that are visible from outside of t,
     but also those declared variables that are visible to the main expression inside t.
-}


hsFDsFromInside:: (Term t, MonadPlus m)=> t-> m ([PName],[PName])
hsFDsFromInside t = do (f,d)<-hsFDsFromInside' t
                       return (nub f, nub d)
   where 
     hsFDsFromInside' = applyTU (once_tdTU (failTU  `adhocTU` mod
                                                    -- `adhocTU` decls
                                                     `adhocTU` decl
                                                     `adhocTU` match
                                                     `adhocTU` exp
                                                     `adhocTU` alt
                                                     `adhocTU` stmts ))
                                                    

     mod ((HsModule loc modName exps imps ds)::HsModuleP)
        = hsFreeAndDeclaredPNs ds  

 {-    decls (ds::[HsDeclP])                    --CHECK THIS.
       = hsFreeAndDeclaredPNs decls 
-}
     match ((HsMatch loc1 (PNT fun _ _) pats rhs ds) ::HsMatchP)
       = do (pf, pd) <-hsFreeAndDeclaredPNs pats
            (rf, rd) <-hsFreeAndDeclaredPNs rhs
            (df, dd) <-hsFreeAndDeclaredPNs ds
            return (nub (pf `union` ((rf `union` df) \\ (dd `union` pd `union` [fun]))), 
                    nub (pd `union` rd `union` dd `union` [fun]))

     decl ((TiDecorate.Dec (HsPatBind loc p rhs ds))::HsDeclP)
      = do (pf, pd)<-hsFreeAndDeclaredPNs p
           (rf, rd)<-hsFreeAndDeclaredPNs rhs
           (df, dd)<-hsFreeAndDeclaredPNs ds 
           return (nub (pf `union` ((rf `union` df) \\ (dd `union` pd))),
                   nub ((pd `union` rd `union` dd)))

     decl (TiDecorate.Dec (HsFunBind loc matches))
         =do fds <-mapM hsFDsFromInside matches
             return (nub (concatMap fst fds), nub(concatMap snd fds))
   
     decl _ = mzero 
 
     exp ((TiDecorate.Exp (HsLet decls exp))::HsExpP)
          = do (df,dd)<- hsFreeAndDeclaredPNs decls
               (ef,_)<- hsFreeAndDeclaredPNs exp 
               return (nub (df `union` (ef \\ dd)), nub dd)
     exp (TiDecorate.Exp (HsLambda pats body))
            = do (pf,pd) <-hsFreeAndDeclaredPNs pats
                 (bf,_) <-hsFreeAndDeclaredPNs body
                 return (nub ((bf `union` pf) \\ pd), nub pd)      
     exp _ = mzero

     alt ((HsAlt _ pat exp decls)::HsAltP)
         = do (pf,pd) <- hsFreeAndDeclaredPNs pat
              (ef,ed) <- hsFreeAndDeclaredPNs exp
              (df,dd) <- hsFreeAndDeclaredPNs decls
              return (nub (pf `union` (((ef \\ dd) `union` df) \\ pd)), nub (pd `union` dd))      

     stmts ((HsLetStmt decls stmts)::HsStmtP)
          = do (df,dd) <-hsFreeAndDeclaredPNs decls
               (sf,sd) <-hsFreeAndDeclaredPNs stmts
               return (nub (df `union` (sf \\dd)),[]) -- dd)

     stmts (HsGenerator _ pat exp stmts) 
          = do (pf,pd) <-hsFreeAndDeclaredPNs pat
               (ef,ed) <-hsFreeAndDeclaredPNs exp
               (sf,sd) <-hsFreeAndDeclaredPNs stmts
               return (nub (pf `union` ef `union` (sf\\pd)),[]) -- pd)
     
     stmts _ = mzero    


-- | The same as `hsFDsFromInside` except that the returned variables are in the String format
hsFDNamesFromInside::(Term t, MonadPlus m)=>t->m ([String],[String])
hsFDNamesFromInside t =do (f,d)<-hsFDsFromInside t
                          return ((nub.map pNtoName) f, (nub.map pNtoName) d)

------------------------------------------------------------------------------------------
-- | Same as `hsVisiblePNs' except that the returned identifiers are in String format.
hsVisibleNames:: (Term t1, Term t2, FindEntity t1, MonadPlus m) => t1 -> t2 -> m [String]
hsVisibleNames e t =do d<-hsVisiblePNs e t
                       return ((nub.map pNtoName) d)
 
-- | Given syntax phrases e and t, if e occurs in  t, then return those vairables
--  which are declared in t and accessible to e, otherwise return []. 
hsVisiblePNs :: (Term t1, Term t2, FindEntity t1, MonadPlus m) => t1 -> t2 -> m [PName]
hsVisiblePNs e t =applyTU (full_tdTU (constTU [] `adhocTU` mod 
                                                  `adhocTU` exp
                                                  `adhocTU` match
                                                  `adhocTU` patBind
                                                  `adhocTU` alt
                                                  `adhocTU` stmts)) t
      where         
          mod ((HsModule loc modName exps imps decls)::HsModuleP)
            |findEntity e decls
           =do (df,dd)<-hsFreeAndDeclaredPNs decls
               return dd
          mod _=return []
                                                             
          exp ((TiDecorate.Exp (HsLambda pats body))::HsExpP)
            |findEntity e body
             = do (pf,pd) <-hsFreeAndDeclaredPNs pats
                  return pd         

          exp (TiDecorate.Exp (HsLet decls e1))
             |findEntity e e1 || findEntity e decls
             = do (df,dd)<- hsFreeAndDeclaredPNs decls
                  return dd      
          exp _ =return [] 
                   
          match (m@(HsMatch _ (PNT fun _ _)  pats rhs  decls)::HsMatchP)
            |findEntity e rhs || findEntity e decls
            = do (pf,pd) <- hsFreeAndDeclaredPNs pats
                 (df,dd) <- hsFreeAndDeclaredPNs decls
                 return  (pd `union` dd `union` [fun])
          match _=return []
 
          patBind (p@(TiDecorate.Dec (HsPatBind _ pat rhs decls))::HsDeclP)
            |findEntity e rhs || findEntity e decls 
             =do (pf,pd) <- hsFreeAndDeclaredPNs pat
                 (df,dd) <- hsFreeAndDeclaredPNs decls
                 return (pd `union` dd)
          patBind _=return [] 

          alt ((HsAlt _ pat exp decls)::HsAltP)
             |findEntity e exp || findEntity e decls
             = do (pf,pd) <- hsFreeAndDeclaredPNs pat
                  (df,dd) <- hsFreeAndDeclaredPNs decls
                  return (pd `union` dd)
          alt _=return []
                    
          stmts ((HsGenerator _ pat exp stmts) :: HsStmtP) 
            |findEntity e stmts
             =do (pf,pd) <-hsFreeAndDeclaredPNs pat
                 return pd

          stmts (HsLetStmt decls stmts)
            |findEntity e decls || findEntity e stmts
             =do (df,dd) <-hsFreeAndDeclaredPNs decls
                 return dd
          stmts _ =return []

-------------------------------------------------------------------------------

{- | The HsDecls class -}
class (Term t) => HsDecls t where  
    -- | Return the declarations that are directly enclosed in the given syntax phrase.
    hsDecls :: t->[HsDeclP]
    -- | Replace the  directly enclosed declaration list by the given declaration list.
    --  Note: This function does not modify the token stream.
    replaceDecls :: t->HsDeclsP->t
   
    -- | Return True if the specified identifier is declared in the given syntax phrase.
    isDeclaredIn :: PName -> t->Bool 

instance HsDecls HsMatchP where   
    hsDecls (HsMatch loc1 fun pats rhs ds@(Decs x y))=x 

    replaceDecls (HsMatch loc1 fun pats rhs ds) ds'
      =(HsMatch loc1 fun pats rhs ds')

    isDeclaredIn  pn match@(HsMatch loc1 (PNT fun _ _) pats rhs ds)
       =fromMaybe False ( do (_,d)<-hsFDsFromInside match
                             Just (elem pn (d \\ [fun])))
instance HsDecls HsDeclP where
    hsDecls (TiDecorate.Dec (HsPatBind loc p rhs ds@(Decs x y)))=x
    hsDecls (TiDecorate.Dec (HsFunBind loc matches))=concatMap hsDecls matches  
    hsDecls _ =[]

    replaceDecls (TiDecorate.Dec (HsPatBind loc p rhs ds)) ds'
        =TiDecorate.Dec (HsPatBind loc p rhs ds')
    replaceDecls x ds' =x

    isDeclaredIn pn (TiDecorate.Dec (HsPatBind loc p rhs ds))
      = fromMaybe False (do (_, rd)<-hsFreeAndDeclaredPNs rhs
                            (_, dd)<-hsFreeAndDeclaredPNs ds
                            Just (elem pn (rd `union` dd)))               
    isDeclaredIn pn _ =False 
    
instance HsDecls HsDeclsP where
    hsDecls ds@(Decs x y) = concatMap hsDecls x
    replaceDecls ds _ = ds
    isDeclaredIn _ ds@(Decs x y) = False

instance HsDecls [HsDeclP] where
    hsDecls ds= concatMap hsDecls ds
    replaceDecls ds _ = ds             -- This should not happen.
    isDeclaredIn _ ds = False            -- This should not happen.

instance HsDecls HsModuleP where
    hsDecls (HsModule loc modName exps imps ds@(Decs x y))=x

    replaceDecls (HsModule loc modName exps imps ds) ds'
       = HsModule loc modName exps imps ds'

    isDeclaredIn pn (HsModule loc modName exps imps ds)
       =fromMaybe False  (do (rf,rd)<-hsFreeAndDeclaredPNs ds
                             Just (elem pn rd))   

instance HsDecls RhsP where
    hsDecls rhs=fromMaybe [] (applyTU (stop_tdTU (failTU `adhocTU` inLet
                                                                        `adhocTU` inAlt
                                                                        `adhocTU` inStmt)) rhs) 
             where inLet ((TiDecorate.Exp (HsLet ds@(Decs x y) e)) ::HsExpP)=Just x
                   inLet _ =mzero

                   inAlt ((HsAlt _ p rhs ds@(Decs x y))::HsAlt HsExpP HsPatP HsDeclsP)=Just x

                   inStmt ((HsLetStmt ds@(Decs x y) _)::HsStmt HsExpP HsPatP HsDeclsP)=Just x
                   inStmt _=mzero

    replaceDecls rhs _ = rhs           -- This should not happen.
    isDeclaredIn _ _  = False            -- This should not happen.

instance HsDecls HsExpP where
    hsDecls rhs=fromMaybe [] (applyTU (stop_tdTU (failTU `adhocTU` inLet
                                                         `adhocTU` inAlt                  
                                                         `adhocTU` inStmt)) rhs) 
             where inLet ((TiDecorate.Exp (HsLet ds@(Decs x y) e)) ::HsExpP)=Just x
                   inLet (TiDecorate.Exp (HsListComp (HsLetStmt ds@(Decs x y) stmts)))=Just x
                   inLet (TiDecorate.Exp (HsDo (HsLetStmt ds@(Decs x y) stmts)))=Just x
                   inLet _ =Nothing

                   inAlt ((HsAlt _ p rhs ds@(Decs x y))::HsAlt HsExpP HsPatP HsDeclsP)=Just x

                   inStmt ((HsLetStmt ds@(Decs x y) _)::HsStmt HsExpP HsPatP HsDeclsP)=Just x
                   inStmt _=Nothing 
    
    replaceDecls (TiDecorate.Exp (HsLet ds e)) ds'
            =if ds'== Decs [] ([], [])
                then e 
                else (TiDecorate.Exp (HsLet ds' e))
                     
    replaceDecls (TiDecorate.Exp (HsListComp (HsLetStmt ds stmts))) ds'@(Decs x y)
            =if x==[] && isLast stmts 
               then (TiDecorate.Exp (HsList [fromJust (expInLast stmts)]))
               else (TiDecorate.Exp (HsListComp (HsLetStmt ds' stmts)))
       where
         isLast (HsLast e)=True
         isLast _=False
         
         expInLast (HsLast e)=Just e
         expInLast _=Nothing

    replaceDecls (TiDecorate.Exp (HsDo (HsLetStmt ds stmts))) ds'@(Decs x y)
            =if x==[] 
                then (TiDecorate.Exp (HsDo stmts))
                else (TiDecorate.Exp (HsDo (HsLetStmt ds' stmts)))
    replaceDecls x ds'=x


    isDeclaredIn pn (TiDecorate.Exp (HsLambda pats body))
            = fromMaybe False (do (pf,pd) <-hsFreeAndDeclaredPNs pats
                                  Just (elem pn  pd))

    isDeclaredIn pn (TiDecorate.Exp (HsLet decls e))        
           =fromMaybe False (do (df,dd)<- hsFreeAndDeclaredPNs decls
                                Just (elem pn dd))
        
    isDeclaredIn pn _=False 
                   

instance HsDecls HsStmtP where
    hsDecls (HsLetStmt ds@(Decs x y) stmts)=x
    hsDecls  _ = []
    
    replaceDecls (HsLetStmt ds stmts) ds'@(Decs x y)
     = if x/=[] then  HsLetStmt ds' stmts         
                  else stmts

    isDeclaredIn pn (HsGenerator _ pat exp stmts) -- Claus
        =fromMaybe False (do (pf,pd) <-hsFreeAndDeclaredPNs pat
                             Just (elem pn pd))

    isDeclaredIn pn (HsLetStmt decls stmts)
        =fromMaybe False (do (df,dd) <-hsFreeAndDeclaredPNs decls
                             Just (elem pn dd))

    isDeclaredIn pn _=False

instance HsDecls HsAltP where
    hsDecls (HsAlt _ p rhs ds@(Decs x y))=x

    replaceDecls (HsAlt loc p rhs ds) ds'=HsAlt loc p rhs ds'

    isDeclaredIn pn (HsAlt _ pat exp decls)
       =fromMaybe False ( do (pf,pd) <- hsFreeAndDeclaredPNs pat
                             (df,dd) <- hsFreeAndDeclaredPNs decls
                             Just (elem pn (pd `union` dd)))
    

-------------------------------------------------------------------------------------------
class (Term a)=>FindEntity a where
  -- | Returns True is a syntax phrase, say a, is part of another syntax phrase, say b.
  findEntity:: (Term b)=> a->b->Bool

instance FindEntity HsExpP  where

  findEntity e b
    =(fromMaybe False)(applyTU (once_tdTU (failTU `adhocTU` inExp)) b)
     where
       inExp (e1::HsExpP)
         | e==e1 =Just True
       inExp _ =Nothing

instance FindEntity PName  where

  findEntity pn b   
   =(fromMaybe False)(applyTU (once_tdTU (failTU `adhocTU` worker)) b)
     where 
        worker (PNT pname _ _ ) 
           |pname==pn= Just True
        worker _ =Nothing 

instance FindEntity PNT where

  findEntity pnt b
   =(fromMaybe False)(applyTU (once_tdTU (failTU `adhocTU` worker)) b)
      where 
        worker (pnt1::PNT)
           |sameOccurrence pnt pnt1 = Just True

        worker _ =Nothing 

     
----------------------------------------------------------------------------------------- 

-- Get the toks for a declaration, and adjust its offset to 0.   
getDeclAndToks pn incSig toks t
    = ghead "getDeclAndToks" $ applyTU (stop_tdTU (failTU `adhocTU` inDecls)) t
  where 
    inDecls decls 
      |snd (break (defines pn) decls) /=[] 
      = return $ getDeclAndToks' pn incSig decls toks 
    inDecls x = mzero 
    
    getDeclAndToks' pn incSig decls toks  
     = let typeSig = if (not incSig)
                      then Nothing
                      else let (decls1,decls2) =break (definesTypeSig pn) decls
                           in if decls2==[] then Nothing else Just (ghead "getDeclAndToks" decls2) 
           (decls1', decls2') = break (defines pn) decls
           decl = if decls2' == [] then error "getDeclAndToks:: declaration does not exisit"
                                   else ghead "getDeclAndToks2" decls2'
           offset = getOffset toks (fst (startEndLoc toks decl))
           declToks =removeOffset offset $ getToks' decl toks
           sigToks = case typeSig of 
                       Nothing  -> []
                       Just (sig@(TiDecorate.Dec (HsTypeSig _ [i] _ _)))-> removeOffset offset $ getToks' sig toks
                       Just (TiDecorate.Dec (HsTypeSig loc is c ty))-> let sig' =(TiDecorate.Dec (HsTypeSig loc0 [nameToPNT (pNtoName pn)] c ty))
                                                            in  tokenise (Pos 0 (-1111) 1) 0 True $ prettyprint sig'++"\n" 
       in  (if isJust typeSig then [fromJust typeSig, decl] else [decl], (sigToks ++ declToks))
       
    getToks' decl toks
      = let (startPos, endPos) = startEndLocIncComments toks decl
            (toks1, _) =let(ts1, (t:ts2'))= break (\t -> tokenPos t == endPos) toks
                        in (ts1++[t], ts2')
        in dropWhile (\t -> tokenPos t /= startPos || isNewLn t) toks1

    removeOffset offset toks 
     = let groupedToks = groupTokensByLine toks
       in  concatMap  (doRmWhites offset) groupedToks

              
{-
-- THIS FUNCTION SHOULD NOT BE IN THE API.
-- | Get the list of tokens which represent the declaration that defines pn.
getDeclToks :: PName           -- ^ The identifier. 
              -> Bool          -- ^ True means type signature should be included.
              -> [HsDeclP]     -- ^ The declaration list in which the identifier is defined.
              -> [PosToken]    -- ^ The input token stream.
              -> [PosToken]    -- ^ The result.
-}
---  IMPORTANT: GET RID OF THE -1111*****************
getDeclToks pn incSig decls toks 
  = let (decls1,decls2) =break (definesTypeSig pn) decls
        typeSig = if decls2==[] then Nothing else Just (ghead "getDeclToks1" decls2) --There may or may not type signature.
        (decls1', decls2') = break (defines pn) decls
        decl = if decls2' == [] then error "getDeclToks:: declaration does not exisit"
                                else ghead "getDeclToks2" decls2'
        declToks = getToks' decl toks
        sigToks 
         = case typeSig of 
            Nothing  -> []
            Just (sig@(TiDecorate.Dec (HsTypeSig _ [i] _ _)))-> getToks' sig toks
            Just (TiDecorate.Dec (HsTypeSig loc is c ty))-> let sig' =(TiDecorate.Dec (HsTypeSig loc0 [nameToPNT (pNtoName pn)] c ty))
                                                 in  tokenise (Pos 0 (-1111) 1) 0 True $ prettyprint sig'++"\n"   
    in if incSig then sigToks ++ declToks  else declToks 
   where   
     getToks' decl toks
          = let (startPos, endPos) = startEndLocIncComments toks decl
                (toks1, _) =let(ts1, (t:ts2'))= break (\t -> tokenPos t == endPos) toks
                            in (ts1++[t], ts2')
            in dropWhile (\t -> tokenPos t /= startPos || isNewLn t) toks1


inRegion t toks beginPos endPos 
  =let (sLoc', eLoc')={-getStartEndLoc-} startEndLoc  toks t
       (sLoc,eLoc)=extendBothSides  toks sLoc' eLoc' isWhite isWhite
   in beginPos>=sLoc && beginPos<=eLoc 


applyRefac refac Nothing fileName
  = do (inscps, exps, mod, toks)<-parseSourceFile fileName
       (mod',((toks',m),_))<-runStateT (refac (inscps, exps, mod)) ((toks,False), (-1000,0)) 
       return ((fileName,m),(toks',mod'))

applyRefac refac (Just (inscps, exps, mod, toks)) fileName
  = do (mod',((toks',m),_))<-runStateT (refac (inscps, exps, mod)) ((toks,False), (-1000,0)) 
       return ((fileName,m),(toks', mod'))  
                                    
applyRefacToClientMods refac fileName
   = do clients <- clientModsAndFiles =<< fileNameToModName fileName
        mapM (applyRefac refac Nothing) (map snd clients)



{-
--this function try to find an identifier through a textual interface. More details will be added.
findPNByPath::String->HsModuleP->Either String PName
findPNByPath path mod 
  = case  findDeclByPath path mod of
      Left errMsg -> Left errMsg
      Right decl  -> Right $ head $ definedPNs decl 
  where     
    findDeclByPath path mod
      = let names = extractPath path
        in findPNByPath' names (hsModDecls mod)
    
    extractPath path = extractPath' [] path
    extractPath' r path =
      case span (/='.') path of
            (name, "")      -> r++[name]
            (name, subPath) -> extractPath' (r++[name]) (tail subPath) 

    findPNByPath' (name:names) [] = Left "Can not find the declaration"
    findPNByPath' (name:names) decls
      = let decl = findDeclByName name decls
        in if decl==[] then Left "Can not find the declaration"
                       else if names==[] then Right (head decl)
                                         else findPNByPath' names (hsDecls (head decl))    
    findDeclByName name decls = filter definesName decls
     where
       definesName (Dec (HsFunBind _ ((HsMatch _ (PNT pn _ _) _ _ _):_)))
          = pNtoName pn == name
       definesName (Dec (HsPatBind _ p _ _)) = name == (pNtoName.head.hsPNs) p 
       definesName  _ = False
-}


-- THe following functions were added Chris Brown to work specifically with the Typed AST
-- created by the type checker

------------------------------------------------------------------------------------------
-- | Collect the free and declared variables (in the PName format) in a given syntax phrase t.
-- In the result, the first list contains the free variables, and the second list contains the declared variables.
removeFromInts :: (MonadPlus m, Term t) => t -> m t
removeFromInts mod
 = do
     let dName = findDname mod
     newMod <- removeFromInts' dName mod
     return newMod
      where 
        findDname t
          = fromMaybe (defaultExp)
             (applyTU (once_tdTU (failTU `adhocTU` findDname))t )
              where
                findDname (TiDecorate.Exp (HsApp (TiDecorate.Exp (HsApp (TiSpec (HsVar (PNT (PN (UnQual "fromInteger") _)_ _))_ _) d)) x)::HsExpP)
                  = Just d
                findDname _ = mzero
                
        removeFromInts' :: (MonadPlus m, Term t) => HsExpP -> t -> m t
        removeFromInts' dName t
          = applyTP (full_tdTP (idTP `adhocTP` remFromInt `adhocTP` (remFromPat dName))) t
             where
              remFromInt (TiDecorate.Exp (HsApp (TiDecorate.Exp (HsApp (TiSpec (HsVar (PNT (PN (UnQual "fromInteger") _)_ _))_ _) d)) x)::HsExpP)
               = return x
              remFromInt e@(_) = return e
       
              remFromPat (TiDecorate.Exp (HsId x)) ((HsMatch t1 t2 ((TiDecorate.Pat (HsPId y)):ps) e ds)::HsMatchI PNT HsExpP HsPatP HsDeclsP)
               | x == y = return (HsMatch t1 t2 ps e ds)
              remFromPat _ e@(_) = return e 

------------------------------------------------------------------------------------------
-- | Takes a [HsDeclP] which is a data type and returns the data type name        
getDataName :: Term t => t -> String
getDataName t
 = fromMaybe ""
    (applyTU (once_tdTU (failTU `adhocTU` inData)) t)
    where
     inData ((HsTyCon (PNT (PN (UnQual x)_) _ _)) :: TI PNT HsTypeP)
       = Just x
     inData _ = mzero  

------------------------------------------------------------------------------------------
-- | CheckTypes takes a string represetation of a type. List types must be supplied in the form
-- | "[]Int" or "[]a"
-- | CheckTypes checks to see whether the type occurs within the syntax phrase
-- | (returns True if an identifier within the syntax phrase is of the type in question    
checkTypes :: Term t => String -> t -> Bool              
checkTypes ty t
 = fromMaybe False ( applyTU (once_tdTU (failTU `adhocTU` inType)) t)
     where
        inType ((HsTyCon (PNT (PN (UnQual x) _) _ _)) :: TI PNT (HsTypeI PNT))
         = if x == ty then Just True else mzero
        inType _ = mzero
        
--| checkTypes takes a string representation of a type, and the name of a pattern match or function 
--| checkTypes calls the ghc typechecker, and returns True if the data type appears within the
--| type of the function.
--| checkTypes also removes the return type of the fuction/pattern as we are only interested in
--| the type of the arguments.
-- checkTypes :: String -> String -> Bool
checkTypes dat name ses = dat `elem` (ghcTypeCheck1 ses name)
        
-- | getPNs take a declaration and returns all the PNames within that declaration 
getPNs :: HsDeclP -> [PName]      
getPNs (TiDecorate.Dec (HsFunBind _ (m:ms) ))
 = checkMatch (m:ms)
    where checkMatch [] = []
          checkMatch ((HsMatch _ _ (p:ps) _ _):ms)
            | (getPN p) /= defaultPN = (getPN p) : checkMatch ms
            | otherwise = checkMatch ms
            
-- | getPNPats takes an expression and returns a list of PNames that occur
-- | within that expression.
getPNPats :: HsExpP -> [PName]            
getPNPats (TiDecorate.Exp (HsCase e pats))
 = checkAlt pats
    where checkAlt [] = []
          checkAlt ((HsAlt loc p e2 ds):ps)
            | p /= (TiDecorate.Pat HsPWildCard) = (getPN p) : checkAlt ps
            | otherwise = checkAlt ps 

-- | getPN takes a pattern and returns the PName belonging to that Pattern.
getPN :: (Term t) => t -> PName            
getPN p 
 = fromMaybe (defaultPN)
             (applyTU (once_tdTU (failTU `adhocTU` inPat)) p)
    where
      inPat (pat::PName)
       = Just pat
      inPat _ = Nothing


-- | mapASTOverTAST maps the normal AST over the type decorated AST, preserving the type information
-- | but also preserving the information from the normal AST. This is to remove the things that the 
-- | type checker places into the AST to resolve types. Such as dictionaries and fromIntegers.
-- | this function is called automatically when you parse a function.      
mapASTOverTAST :: (MonadPlus m, Term t, Term t1) => t -> t1 -> m t1
mapASTOverTAST ast tast
 = applyTP (full_tdTP (idTP `adhocTP` inTAST)) tast
     where
       inTAST a@(TiDecorate.Exp (HsApp e1 e2))
         = do
              x <- mapASTOverTAST ast e1
              y <- mapASTOverTAST ast e2
              if x == defaultExp then return y
                                 else if y == defaultExp then return x
                                                         else return a
       inTAST a@(TiSpec i _ _)
         = do 
              return $ findExpAst ast a
      
       inTAST a@(_) = return a
       
       inTPAT a@(TiPSpec i _ _)
         = do
              return $ findPatAst ast a
              
       findPatAst :: Term t => t -> HsPatP -> HsPatP
       findPatAst ast pat
        = fromMaybe (defaultPat)
         (applyTU (once_tdTU (failTU `adhocTU` (inPat pat))) ast)
           where
             inPat a@(TiPSpec i _ _) b@(PosSyntax.Pat (HsPId i2))
              | i == i2   = Just a
              | otherwise = mzero
             inPat a b = mzero

       findExpAst :: Term t => t -> HsExpP -> HsExpP
       findExpAst ast exp
        = fromMaybe (defaultExp)
          ( applyTU (once_tdTU (failTU `adhocTU` (inExp exp)))  ast)
            where
              inExp a@(TiSpec i _ _) b@(PosSyntax.Exp (HsInfixApp e1 i2 e2))
               | i == i2 = Just a
               | otherwise = mzero
              inExp a@(TiSpec i _ _) b@(PosSyntax.Exp (HsLeftSection e i2))
               | i == i2 = Just a
               | otherwise = mzero
              inExp a@(TiSpec i _ _) b@(PosSyntax.Exp (HsRightSection i2 e))
               | i == i2 = Just a
               | otherwise = mzero
              inExp a@(TiSpec i _ _) b@(PosSyntax.Exp (HsId i2))
               | i == i2 = Just a
               | otherwise = mzero
              inExp a b = mzero
               
