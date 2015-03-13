{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

--------------------------------------------------------------------------------
-- Module      : TypeUtils

-- Maintainer  : refactor-fp\@kent.ac.uk
-- |
--
-- This module contains a collection of program analysis and
-- transformation functions (the API) that work over the Type
-- Decorated AST. Most of the functions defined in the module are
-- taken directly from the API, but in some cases are modified to work
-- with the type decorated AST.
--
-- In particular some new functions have been added to make type
-- decorated AST traversals easier.
--
-- In HaRe, in order to preserve the comments and layout of refactored
-- programs, a refactoring modifies not only the AST but also the
-- token stream, and the program source after the refactoring is
-- extracted from the token stream rather than the AST, for the
-- comments and layout information is kept in the token steam instead
-- of the AST. As a consequence, a program transformation function
-- from this API modifies both the AST and the token stream (unless
-- explicitly stated). So when you build your own program
-- transformations, try to use the API to do the transformation, as
-- this can liberate you from caring about the token stream.
--
-- This type decorated API is still in development. Any suggestions
-- and comments are very much welcome.


--------------------------------------------------------------------------------
module Language.Haskell.Refact.Utils.TypeUtils
       (
 -- * Program Analysis
    -- ** Imports and exports
    inScopeInfo, isInScopeAndUnqualified, isInScopeAndUnqualifiedGhc, inScopeNames
   , isExported, isExplicitlyExported, modIsExported

    -- ** Variable analysis
    , isFieldName
    , isClassName
    , isInstanceName
    ,hsPNs
    ,isDeclaredIn
    ,hsFreeAndDeclaredPNsOld
    ,hsFreeAndDeclaredNameStrings
    ,hsFreeAndDeclaredPNs
    ,hsFreeAndDeclaredGhc
    ,getDeclaredTypes
    ,getFvs, getFreeVars, getDeclaredVars
    ,hsVisiblePNs, hsVisibleNames
    ,hsFDsFromInside, hsFDNamesFromInside
    ,hsVisibleDs

    -- ** Property checking
    ,isVarId,isConId,isOperator,isTopLevelPN,isLocalPN,isNonLibraryName
    ,isQualifiedPN, isFunOrPatName, isTypeSig
    ,isFunBindP,isFunBindR,isPatBindP,isPatBindR,isSimplePatBind
    ,isComplexPatBind,isFunOrPatBindP,isFunOrPatBindR
    ,usedWithoutQualR,isUsedInRhs

    -- ** Getting
    ,findPNT,findPN,findAllNameOccurences
    ,findPNs, findEntity, findEntity'
    ,findIdForName
    ,getTypeForName

    ,sameOccurrence
    ,defines, definesP,definesTypeSig
    -- ,HasModName(hasModName), HasNameSpace(hasNameSpace)
    ,sameBind
    {- ,usedByRhs -},UsedByRhs(..)

    -- ** Modules and files
    -- ,clientModsAndFiles,serverModsAndFiles,isAnExistingMod
    -- ,fileNameToModName, strToModName, modNameToStr
    , isMainModule
    , getModule

    -- ** Locations
    ,defineLoc, useLoc, locToExp
    ,locToName, locToRdrName
    ,getName

 -- * Program transformation
    -- ** Adding
    ,addDecl, addItemsToImport, addHiding
    ,addParamsToDecls, addActualParamsToRhs, addImportDecl, duplicateDecl
    -- ** Removing
    ,rmDecl, rmTypeSig, rmTypeSigs -- , commentOutTypeSig, rmParams
    -- ,rmItemsFromExport, rmSubEntsFromExport, Delete(delete)

    -- ** Updating
    -- ,Update(update)
    {- ,qualifyPName-},rmQualifier,qualifyToplevelName,renamePN {- ,replaceNameInPN -},autoRenameLocalVar

    -- * Miscellous
    -- ** Parsing, writing and showing
    {- ,parseSourceFile,writeRefactoredFiles-}, showEntities,showPNwithLoc -- , newProj, addFile, chase
    -- ** Locations
    -- ,toRelativeLocs, rmLocs
    -- ** Default values
   ,defaultPN {- ,defaultPNT -},defaultName {-,defaultModName-},defaultExp -- ,defaultPat, defaultExpUnTyped


    -- ** Identifiers, expressions, patterns and declarations
    ,ghcToPN,lghcToPN, expToName
    ,nameToString
    {- ,expToPNT, expToPN, nameToExp,pNtoExp -},patToPNT {- , patToPN --, nameToPat -},pNtoPat
    {- ,definingDecls -}, definedPNs
    , definingDeclsNames, definingDeclsNames', definingSigsNames
    , definingTyClDeclsNames
    , allNames
    -- ,simplifyDecl

    -- ** Others
    , mkRdrName,mkNewGhcName,mkNewName,mkNewToplevelName

    -- The following functions are not in the the API yet.
    , causeNameClashInExports {- , inRegion , unmodified -}

    , removeOffset

    -- * Typed AST traversals (added by CMB)
    -- * Miscellous
    -- ,removeFromInts, getDataName, checkTypes, getPNs, getPN, getPNPats, mapASTOverTAST

    -- * Debug stuff
    , getDeclAndToks, getSigAndToks
    , getToksForDecl, removeToksOffset -- ++AZ++ remove this after debuggging
    , getParsedForRenamedLPat
    , getParsedForRenamedName
    , getParsedForRenamedLocated
    -- , allPNT
    --  , allPNTLens
    -- , newNameTok
    , stripLeadingSpaces
    -- , lookupNameGhc
 ) where

-- import Control.Monad.IO.Class ()
import Control.Monad.State
import Data.Char
import Data.List
import Data.Maybe
import Data.Monoid
import Exception

import Language.Haskell.Refact.Utils.Binds
import Language.Haskell.Refact.Utils.GhcUtils
import Language.Haskell.Refact.Utils.GhcVersionSpecific
import Language.Haskell.Refact.Utils.LocUtils
import Language.Haskell.Refact.Utils.Monad
import Language.Haskell.Refact.Utils.MonadFunctions
import Language.Haskell.Refact.Utils.TokenUtils
import Language.Haskell.Refact.Utils.TypeSyn

import Language.Haskell.TokenUtils.GHC.Layout
import Language.Haskell.TokenUtils.TokenUtils
import Language.Haskell.TokenUtils.Types
import Language.Haskell.TokenUtils.Utils

-- Modules from GHC
import qualified Bag           as GHC
-- import qualified BasicTypes    as GHC
import qualified FastString    as GHC
import qualified GHC           as GHC
-- import qualified Lexer         as GHC hiding (getSrcLoc)
import qualified Module        as GHC
import qualified Name          as GHC
import qualified NameSet       as GHC
import qualified Outputable    as GHC
import qualified RdrName       as GHC
import qualified SrcLoc        as GHC
import qualified UniqSet       as GHC
import qualified Unique        as GHC
import qualified Var           as GHC

import qualified Data.Generics as SYB
import qualified GHC.SYB.Utils as SYB

import Data.Generics.Strafunski.StrategyLib.StrategyLib hiding (liftIO,MonadPlus,mzero)

-- ---------------------------------------------------------------------

-- | For free variables
data FreeNames = FN [GHC.Name]

-- | For declared variables
data DeclaredNames = DN [GHC.Name]

instance Show FreeNames where
  show (FN ls) = "FN " ++ showGhc ls

instance Show DeclaredNames where
  show (DN ls) = "DN " ++ showGhc ls

instance Monoid FreeNames where
  mempty = FN []
  mappend (FN a) (FN b) = FN (a `mappend` b)

instance Monoid DeclaredNames where
  mempty = DN []
  mappend (DN a) (DN b) = DN (a `mappend` b)


emptyFD :: (FreeNames,DeclaredNames)
emptyFD = (FN [], DN [])

-- ---------------------------------------------------------------------
-- |Process the inscope relation returned from the parsing and module
-- analysis pass, and return a list of four-element tuples. Each tuple
-- contains an identifier name, the identifier's namespace info, the
-- identifier's defining module name and its qualifier name.
--
-- The same identifier may have multiple entries in the result because
-- it may have different qualifiers. This makes it easier to decide
-- whether the identifier can be used unqualifiedly by just checking
-- whether there is an entry for it with the qualifier field being
-- Nothing.
--
inScopeInfo :: InScopes                                      -- ^ The inscope relation .
           ->[(String, GHC.NameSpace, GHC.ModuleName, Maybe GHC.ModuleName)] -- ^ The result
inScopeInfo names = nub $  map getEntInfo $ names
  where
     getEntInfo name
       =(showGhc name,
         GHC.occNameSpace $ GHC.nameOccName name,
         GHC.moduleName $ GHC.nameModule name,
         getQualMaybe $ GHC.nameRdrName name)

     getQualMaybe rdrName = case rdrName of
       GHC.Qual modName _occName -> Just modName
       _                         -> Nothing



-- | Return True if the identifier is inscope and can be used without
-- a qualifier.
isInScopeAndUnqualified::String       -- ^ The identifier name.
                       ->InScopes     -- ^ The inscope relation
                       ->Bool         -- ^ The result.
isInScopeAndUnqualified n names
 = isJust $ find (\ (x, _,_, qual) -> x == n && isNothing qual ) $ inScopeInfo names

-- | Return True if the identifier is inscope and can be used without
-- a qualifier. The identifier name string may have a qualifier
-- already
-- NOTE: may require qualification based on name clash with an
-- existing identifier.
isInScopeAndUnqualifiedGhc ::
     String           -- ^ The identifier name.
  -> (Maybe GHC.Name) -- ^ Existing name, to be excluded from test, if
                      --   known
  -> RefactGhc Bool   -- ^ The result.
isInScopeAndUnqualifiedGhc n maybeExising = do
  names <- ghandle handler (GHC.parseName n)
  logm $ "isInScopeAndUnqualifiedGhc:(n,(maybeExising,names))=" ++ (show n) ++ ":" ++  (showGhc (maybeExising,names))
  ctx <- GHC.getContext
  logm $ "isInScopeAndUnqualifiedGhc:ctx=" ++ (showGhc ctx)
  let nameList = case maybeExising of
                  Nothing -> names
                  -- Just n' -> filter (\x -> (GHC.nameUnique x) /= (GHC.nameUnique n')) names
                  Just n' -> filter (\x -> (showGhc x) /= (showGhc n')) names
  logm $ "isInScopeAndUnqualifiedGhc:(n,nameList)=" ++ (show n) ++ ":" ++  (showGhc nameList)
  return $ nameList /= []

  where
    handler:: SomeException -> RefactGhc [GHC.Name]
    handler e = do
      logm $ "isInScopeAndUnqualifiedGhc.handler e=" ++ (show e)
      return []

inScopeNames :: String         -- ^ The identifier name.
             -> RefactGhc [GHC.Name] -- ^ The result.
inScopeNames n = do
  names <- ghandle handler (GHC.parseName n)
  logm $ "inScopeNames:(n,names)=" ++ (show n) ++ ":" ++  (showGhc names)
  return $ names

  where
    handler:: SomeException -> RefactGhc [GHC.Name]
    handler e = do
      logm $ "inScopeNames.handler e=" ++ (show e)
      return []

-- ---------------------------------------------------------------------
-- | Show a PName in a format like: 'pn'(at row:r, col: c).
showPNwithLoc:: GHC.Located GHC.Name -> String
showPNwithLoc pn@(GHC.L l _n)
  = let (r,c) = getGhcLoc l
    -- in  " '"++pNtoName pn++"'" ++"(at row:"++show r ++ ",col:" ++ show c ++")"
    in  " '"++showGhc pn++"'" ++"(at row:"++show r ++ ",col:" ++ show c ++")"

-- ---------------------------------------------------------------------

defaultPN :: PName
defaultPN = PN (mkRdrName "nothing")

defaultName :: GHC.Name
defaultName = n
  where
    un = GHC.mkUnique 'H' 0 -- H for HaRe :)
    n = GHC.localiseName $ GHC.mkSystemName un (GHC.mkVarOcc "nothing")

-- | Default expression.
defaultExp::HsExpP
-- defaultExp=Exp (HsId (HsVar defaultPNT))
defaultExp=GHC.HsVar $ mkRdrName "nothing"


mkRdrName :: String -> GHC.RdrName
mkRdrName s = GHC.mkVarUnqual (GHC.mkFastString s)

-- | Make a new GHC.Name, using the Unique Int sequence stored in the
-- RefactState.
mkNewGhcName :: Maybe GHC.Module -> String -> RefactGhc GHC.Name
mkNewGhcName maybeMod name = do
  s <- get
  u <- gets rsUniqState
  put s { rsUniqState = (u+1) }

  let un = GHC.mkUnique 'H' (u+1) -- H for HaRe :)
      -- n = GHC.mkSystemName un (GHC.mkVarOcc name)
      n = case maybeMod of
               Nothing -> GHC.localiseName $ GHC.mkSystemName un (GHC.mkVarOcc name)
               Just modu -> GHC.mkExternalName un modu (GHC.mkVarOcc name) nullSrcSpan
  return n

mkNewToplevelName :: GHC.Module -> String -> GHC.SrcSpan -> RefactGhc GHC.Name
mkNewToplevelName modid name defLoc = do
  s <- get
  u <- gets rsUniqState
  put s { rsUniqState = (u+1) }

  let un = GHC.mkUnique 'H' (u+1) -- H for HaRe :)
      -- n = GHC.mkSystemName un (GHC.mkVarOcc name)
      -- n = GHC.localiseName $ GHC.mkSystemName un (GHC.mkVarOcc name)

        -- mkExternalName :: Unique -> Module -> OccName -> SrcSpan -> Name
      n = GHC.mkExternalName un modid (GHC.mkVarOcc name) defLoc
  return n

---------------------------------------------------------------------------


-- |Create a new name base on the old name. Suppose the old name is 'f', then
--  the new name would be like 'f_i' where 'i' is an integer.
mkNewName::String      -- ^ The old name
          ->[String]   -- ^ The set of names which the new name cannot take
          ->Int        -- ^ The posfix value
          ->String     -- ^ The result
mkNewName oldName fds suffix
  =let newName=if suffix==0 then oldName
                            else oldName++"_"++ show suffix
   in if elem newName fds
        then mkNewName oldName fds (suffix+1)
        else newName

-- ---------------------------------------------------------------------

-- | Return True if the current module is exported either by default
-- or by specifying the module name in the export.
modIsExported:: GHC.ModuleName       -- ^ The module name
               -> GHC.RenamedSource  -- ^ The AST of the module
               -> Bool               -- ^ The result
modIsExported modName (_g,_emps,mexps,_mdocs)
   = let
       modExported (GHC.L _ (GHC.IEModuleContents name)) = name == modName
       modExported _ = False

       moduleExports = filter modExported $ fromMaybe [] mexps

     in if isNothing mexps
           then True
           else (nonEmptyList moduleExports)

-- ---------------------------------------------------------------------

-- | Return True if an identifier is exported by the module currently
-- being refactored.
isExported :: GHC.Name -> RefactGhc Bool
isExported n = do
  typechecked <- getTypecheckedModule
  let modInfo = GHC.tm_checked_module_info typechecked
  return $ GHC.modInfoIsExportedName modInfo n

-- ---------------------------------------------------------------------

-- | Return True if an identifier is explicitly exported by the module.
isExplicitlyExported::GHC.Name           -- ^ The identifier
                     ->GHC.RenamedSource -- ^ The AST of the module
                     ->Bool              -- ^ The result
isExplicitlyExported pn (_g,_imps,exps,_docs)
  = findEntity pn exps

-- ---------------------------------------------------------------------


-- | Check if the proposed new name will conflict with an existing export
causeNameClashInExports::  GHC.Name          -- ^ The original name
                        -> GHC.Name          -- ^ The new name
                        -> GHC.ModuleName    -- ^ The identity of the module
                        -> GHC.RenamedSource -- ^ The AST of the module
                        -> Bool              -- ^ The result

-- Note that in the abstract representation of exps, there is no qualified entities.
causeNameClashInExports pn newName modName renamed@(_g,imps,maybeExps,_doc)
  = let exps = fromMaybe [] maybeExps
        varExps = filter isImpVar exps
        -- TODO: make withoutQual part of the API
        withoutQual n = showGhc $ GHC.localiseName n
        modNames=nub (concatMap (\(GHC.L _ (GHC.IEVar x))->if withoutQual x== withoutQual newName
                                                        then [GHC.moduleName $ GHC.nameModule x]
                                                        else []) varExps)
        res = (isExplicitlyExported pn renamed) &&
               ( any (modIsUnQualifedImported renamed) modNames
                 || elem modName modNames)
    in res
 where
    isImpVar (GHC.L _ x) = case x of
      GHC.IEVar _ -> True
      _           -> False

    modIsUnQualifedImported _mod' modName'
     =let -- imps =hsModImports mod
       -- imp@(GHC.L _ (GHC.ImportDecl (GHC.L _ modName) qualify _source _safe isQualified _isImplicit as h))
      in isJust $ find (\(GHC.L _ (GHC.ImportDecl (GHC.L _ modName1) _qualify _source _safe isQualified _isImplicit _as _h))
                                -> modName1 == modName' && (not isQualified)) imps
      -- in isJust $ find (\(HsImportDecl _ (SN modName1 _) qualify  _ h) -> modName == modName1 && (not qualify)) imps


-- Original seems to be
--   1. pick up any module names in the export list with same unQual
     --   part as the new name
--   2. Check if the old is exported explicitly
--   3.  if so, if the new module is exported unqualified
--        or belongs to the current module
--       then it will cause a clash

-- ---------------------------------------------------------------------
-- | Collect the free and declared variables (in the GHC.Name format)
-- in a given syntax phrase t. In the result, the first list contains
-- the free variables, and the second list contains the declared
-- variables.
-- Expects RenamedSource
hsFreeAndDeclaredPNsOld:: (SYB.Data t) => t -> ([GHC.Name],[GHC.Name])
hsFreeAndDeclaredPNsOld t = res
  where
    fd = hsFreeAndDeclaredPNs' t
    (f,d) = fromMaybe ([],[]) fd
    res = (f \\ d, d)

hsFreeAndDeclaredPNs':: (SYB.Data t) => t -> Maybe ([GHC.Name],[GHC.Name])
hsFreeAndDeclaredPNs' t = do
      (f,d) <- hsFreeAndDeclared'
      let (f',d') = (nub f, nub d)
      -- return (f' \\ d',d')
      return (f',d')
          -- hsFreeAndDeclared'=applyTU (stop_tdTU (failTU  `adhocTU` exp

   where

          hsFreeAndDeclared' = applyTU (stop_tdTUGhc (failTU
                                                         `adhocTU` expr
                                                         `adhocTU` pattern
                                                         `adhocTU` binds
                                                         `adhocTU` bindList
                                                         `adhocTU` match
                                                         `adhocTU` stmts
                                                         `adhocTU` rhs
                                                          )) t

          -- TODO: ++AZ++ Note:After renaming, HsBindLR has field bind_fvs
          --       containing locally bound free vars

          -- expr --
          expr (GHC.HsVar n) = return ([n],[])

          expr (GHC.OpApp e1 (GHC.L _ (GHC.HsVar n)) _ e2) = do
              efed <- hsFreeAndDeclaredPNs' [e1,e2]
              fd   <- addFree n efed
              return fd

          expr ((GHC.HsLam (GHC.MatchGroup matches _)) :: GHC.HsExpr GHC.Name) =
             hsFreeAndDeclaredPNs' matches

          expr ((GHC.HsLet decls e) :: GHC.HsExpr GHC.Name) =
            do
              (df,dd) <- hsFreeAndDeclaredPNs' decls
              (ef,_)  <- hsFreeAndDeclaredPNs' e
              return ((df `union` (ef \\ dd)),[])

          expr (GHC.RecordCon (GHC.L _ n) _ e) = do
            fd <- (hsFreeAndDeclaredPNs' e)
            addFree n fd   --Need Testing

          expr (GHC.EAsPat (GHC.L _ n) e) = do
            fd <- (hsFreeAndDeclaredPNs' e)
            addFree n fd

          expr _ = mzero


          -- rhs --
          rhs ((GHC.GRHSs g ds) :: GHC.GRHSs GHC.Name)
            = do (df,dd) <- hsFreeAndDeclaredPNs' g
                 (ef,ed) <- hsFreeAndDeclaredPNs' ds
                 return (df ++ ef, dd ++ ed)


          -- pat --
          pattern (GHC.VarPat n) = return ([],[n])
          -- It seems all the GHC pattern match syntax elements end up
          -- with GHC.VarPat

          pattern _ = mzero
          -- pattern _ = return ([],[])

          bindList (ds :: [GHC.LHsBind GHC.Name])
            =do (f,d) <- hsFreeAndDeclaredList ds
                return (f\\d,d)
          -- bindList _ = mzero

          -- match and patBind, same type--
          binds ((GHC.FunBind (GHC.L _ n) _ (GHC.MatchGroup matches _) _ _fvs _) :: GHC.HsBind GHC.Name)
            = do
                (pf,_pd) <- hsFreeAndDeclaredPNs' matches

                return (pf \\ [n] ,[n])

          -- patBind --
          binds (GHC.PatBind pat prhs _ ds _) =
            do
              (pf,pd) <- hsFreeAndDeclaredPNs' pat
              (rf,rd) <- hsFreeAndDeclaredPNs' prhs
              return (pf `union` (rf \\pd),pd ++ GHC.uniqSetToList ds ++ rd)

          binds _ = mzero

          match ((GHC.Match pats _mtype mrhs) :: GHC.Match GHC.Name )
            = do
              (pf,pd) <- hsFreeAndDeclaredPNs' pats
              (rf,rd) <- hsFreeAndDeclaredPNs' mrhs
              return ((pf `union` (rf \\ (pd `union` rd))),[])

          -- stmts --
          stmts ((GHC.BindStmt pat expre _bindOp _failOp) :: GHC.Stmt GHC.Name) = do
            -- TODO ++AZ++ : Not sure it is meaningful to pull
            --               anything out of bindOp/failOp
            (pf,pd)  <- hsFreeAndDeclaredPNs' pat
            (ef,_ed) <- hsFreeAndDeclaredPNs' expre
            let sf1 = []
            return (pf `union` ef `union` (sf1\\pd),[]) -- pd) -- Check this

          stmts ((GHC.LetStmt binds') :: GHC.Stmt GHC.Name) =
            hsFreeAndDeclaredPNs' binds'

          stmts _ = mzero


          addFree :: GHC.Name -> ([GHC.Name],[GHC.Name])
                  -> Maybe ([GHC.Name],[GHC.Name])
          addFree free (fr,de) = return ([free] `union` fr, de)

          hsFreeAndDeclaredList l=do fds<-mapM hsFreeAndDeclaredPNs' l
                                     return (foldr union [] (map fst fds),
                                             foldr union [] (map snd fds))



-- |The same as `hsFreeAndDeclaredPNs` except that the returned
-- variables are in the String format.
hsFreeAndDeclaredNameStrings::(SYB.Data t,GHC.Outputable t) => t -> RefactGhc ([String],[String])
hsFreeAndDeclaredNameStrings t = do
  (f1,d1) <- hsFreeAndDeclaredPNs t
  return ((nub.map showGhc) f1, (nub.map showGhc) d1)


hsFreeAndDeclaredPNs :: (SYB.Data t, GHC.Outputable t) => t -> RefactGhc ([GHC.Name],[GHC.Name])
hsFreeAndDeclaredPNs t = do
  -- logm $ "hsFreeAndDeclaredPNs:t=" ++ (showGhc t)
  (FN f,DN d) <- hsFreeAndDeclaredGhc t
  return (f,d)

-- ---------------------------------------------------------------------

-- | Collect the free and declared variables (in the GHC.Name format)
-- in a given syntax phrase t. In the result, the first list contains
-- the free variables, and the second list contains the declared
-- variables.
-- TODO: use GHC.NameSet instead of lists for FreeNames/DeclaredNames
-- NOTE: The GHC fvs fields only carry non-GHC values, as they are
-- used in the renaming process
hsFreeAndDeclaredGhc :: (SYB.Data t, GHC.Outputable t) => t -> RefactGhc (FreeNames,DeclaredNames)
hsFreeAndDeclaredGhc t = do
  -- logm $ "hsFreeAndDeclaredGhc:t=" ++ showGhc t
  (FN f,DN d) <- res
  let f' = nub f
  let d' = nub d
  -- logm $ "hsFreeAndDeclaredGhc:res=" ++ showGhc (f',d')
  return (FN (f' \\ d'), DN d')

  where
    res = (const err -- emptyFD
          `SYB.extQ` renamed
          `SYB.extQ` lhsbind
          `SYB.extQ` hsbind
          `SYB.extQ` lhsbinds
          `SYB.extQ` lhsbindslrs
          `SYB.extQ` lhsbindslr
          `SYB.extQ` hslocalbinds
          `SYB.extQ` hsvalbinds
          `SYB.extQ` lpats
          `SYB.extQ` lpat
#if __GLASGOW_HASKELL__ > 704
          `SYB.extQ` bndrs
#endif
          `SYB.extQ` ltydecls
          `SYB.extQ` ltydecl
#if __GLASGOW_HASKELL__ > 704
          `SYB.extQ` lfaminstdecls
          `SYB.extQ` lfaminstdecl
#endif
          `SYB.extQ` lsigs
          `SYB.extQ` lsig
          `SYB.extQ` lexprs
          `SYB.extQ` lexpr
          `SYB.extQ` expr
          `SYB.extQ` name
          `SYB.extQ` lstmts
          `SYB.extQ` lstmt
          `SYB.extQ` lhstype
          `SYB.extQ` hstype
          `SYB.extQ` grhs_s
          `SYB.extQ` grhs
          `SYB.extQ` grhsss
          `SYB.extQ` grhss
          `SYB.extQ` matchgroup
          `SYB.extQ` lmatches
          `SYB.extQ` lmatch
          `SYB.extQ` hsrecordbinds
          `SYB.extQ` hsrecordbind
          ) t

    renamed :: GHC.RenamedSource ->  RefactGhc (FreeNames,DeclaredNames)
    renamed (g,_i,_e,_d) = do
      gfds <- hsFreeAndDeclaredGhc $ GHC.hs_valds g
      let tds = concatMap getDeclaredTypes $ concat (GHC.hs_tyclds g)
      return $ gfds <> (FN [],DN tds)


    lhsbinds :: [GHC.LHsBind GHC.Name] -> RefactGhc (FreeNames,DeclaredNames)
    lhsbinds bs = do
      (FN fn,DN dn) <- recurseList bs
      let r = (FN (fn \\ dn),DN dn)
      -- logm $ "hsFreeAndDeclaredGhc.hsbinds:r=" ++ (show r)
      return r

    lhsbind :: GHC.LHsBind GHC.Name -> RefactGhc (FreeNames,DeclaredNames)
    lhsbind (GHC.L _ b) = hsFreeAndDeclaredGhc b

    -- -----------------------

    hsbind :: GHC.HsBind GHC.Name -> RefactGhc (FreeNames,DeclaredNames)
    hsbind b@(GHC.FunBind _n _ (GHC.MatchGroup matches _) _ _ _) = do
        -- logm $ "hsFreeAndDeclaredGhc.hsbind:b=" ++ (showGhc b)
        let d = GHC.collectHsBindBinders b
        -- let pats = concatMap (\(GHC.L _ (GHC.Match pat _ _)) -> pat) matches
        (fp,_dp) <- hsFreeAndDeclaredGhc matches
        -- logm $ "hsFreeAndDeclaredGhc.hsbind:(fp,_dp)=" ++ (show (fp,_dp))
        -- logm $ "hsFreeAndDeclaredGhc.hsbind:(d)=" ++ (showGhc (d))
        let r = (fp,DN []) <> (FN [],DN d)
        -- logm $ "hsFreeAndDeclaredGhc.hsbind:r=" ++ (show (r))
        return $ r
    hsbind b@(GHC.PatBind pa rhs _ _ _) = do
        -- logm $ "hsFreeAndDeclaredGhc.hsbind.PatBind:b=" ++ (showGhc b)
        let d = GHC.collectHsBindBinders b
        (FN fr,DN _dr) <- hsFreeAndDeclaredGhc rhs
        (fp,_) <- lpat pa
        -- logm $ "hsFreeAndDeclaredGhc.hsbind.PatBind:f=" ++ (showGhc fr)
        return $ (fp,DN []) <> (FN fr,DN d)
    hsbind b = do
        -- logm $ "hsFreeAndDeclaredGhc.hsbind:b=" ++ (showGhc b)
        let d = GHC.collectHsBindBinders b
        return (FN [],DN d)

    -- -----------------------

    lhsbindslrs :: [GHC.LHsBindsLR GHC.Name GHC.Name] -> RefactGhc (FreeNames,DeclaredNames)
    lhsbindslrs bs = recurseList bs

    -- -----------------------

    lhsbindslr :: GHC.LHsBindsLR GHC.Name GHC.Name -> RefactGhc (FreeNames,DeclaredNames)
    lhsbindslr bs = do
      hsFreeAndDeclaredGhc $ GHC.bagToList bs

    hslocalbinds :: GHC.HsLocalBinds GHC.Name -> RefactGhc (FreeNames,DeclaredNames)
    hslocalbinds (GHC.HsValBinds binds) = hsFreeAndDeclaredGhc binds
    hslocalbinds (GHC.HsIPBinds binds)  = hsFreeAndDeclaredGhc binds
    hslocalbinds GHC.EmptyLocalBinds    = return emptyFD


    hsvalbinds :: GHC.HsValBinds GHC.Name -> RefactGhc (FreeNames,DeclaredNames)
    hsvalbinds (GHC.ValBindsIn binds sigs) = do
      bfds <- hsFreeAndDeclaredGhc binds
      sfds <- hsFreeAndDeclaredGhc sigs
      return $ bfds <> sfds
    hsvalbinds (GHC.ValBindsOut binds sigs) = do
      bfds <- hsFreeAndDeclaredGhc $ map snd binds
      sfds <- hsFreeAndDeclaredGhc sigs
      return $ bfds <> sfds

    -- -----------------------

    lpats :: [GHC.LPat GHC.Name] -> RefactGhc (FreeNames,DeclaredNames)
    lpats xs = recurseList xs

    -- -----------------------

    lpat :: GHC.LPat GHC.Name -> RefactGhc (FreeNames,DeclaredNames)
    lpat lp@(GHC.L _ p) = do
      -- logm $ "hsFreeAndDeclaredGhc.lpat:" ++ (showGhc lp)
      let
        dn = GHC.collectPatBinders lp

      -- logm $ "hsFreeAndDeclaredGhc.lpat p=" ++ (SYB.showData SYB.Renamer 0 p)

      (FN fn,DN _dn) <- pat p
      -- logm $ "hsFreeAndDeclaredGhc.lpat:(fn,dn)=" ++ (showGhc (fn,dn))
      return (FN fn,DN dn)

    pat :: GHC.Pat GHC.Name -> RefactGhc (FreeNames,DeclaredNames)
    pat (GHC.WildPat _) = return emptyFD
    pat (GHC.VarPat n) = return (FN [],DN [n])
    pat (GHC.LazyPat (GHC.L _ p)) = pat p
    pat (GHC.AsPat (GHC.L _ n) (GHC.L _ p)) = do
      fd <- pat p
      return $ (FN [], DN [n]) <> fd
    pat (GHC.ParPat (GHC.L _ p)) = pat p
    pat (GHC.BangPat (GHC.L _ p)) = pat p
    pat (GHC.ListPat ps _) = do
      fds <- mapM pat $ map GHC.unLoc ps
      return $ mconcat fds
    pat (GHC.TuplePat ps _ _) = do
      fds <- mapM pat $ map GHC.unLoc ps
      return $ mconcat fds
    pat (GHC.PArrPat ps _) = do
      fds <- mapM pat $ map GHC.unLoc ps
      return $ mconcat fds
    pat (GHC.ConPatIn (GHC.L _ n) det) = do
      -- logm $ "hsFreeAndDeclaredGhc.pat.ConPatIn:details=" ++ (SYB.showData SYB.Renamer 0 det)
      (FN f,DN _d) <- details det
      return $ (FN [n],DN []) <> (FN [],DN f)
    -- pat (GHC.ConPatOut )
    pat (GHC.ViewPat e (GHC.L _ p) _) = do
      fde <- hsFreeAndDeclaredGhc e
      fdp <- pat p
      return $ fde <> fdp
    -- pat (GHC.QuasiQuotePat _)
    pat (GHC.LitPat _) = return emptyFD
    pat (GHC.NPat _ _ _) = return emptyFD
    pat (GHC.NPlusKPat (GHC.L _ n) _ _ _) = return (FN [],DN [n])
    pat _p@(GHC.SigPatIn (GHC.L _ p) b) = do
      fdp <- pat p
      (FN fb,DN _db) <- hsFreeAndDeclaredGhc b
#if __GLASGOW_HASKELL__ > 704
      return $ fdp <> (FN fb,DN [])
#else
      return $ fdp <> (FN _db,DN [])
#endif
    pat (GHC.SigPatOut (GHC.L _ p) _) = pat p
    pat (GHC.CoPat _ p _) = pat p

    pat p = error $ "hsFreeAndDeclaredGhc.pat:unimplemented:" ++ (showGhc p)

    --  HsConDetails (LPat id) (HsRecFields id (LPat id))
    details :: GHC.HsConPatDetails GHC.Name -> RefactGhc (FreeNames,DeclaredNames)
    details (GHC.PrefixCon  args) = do
      -- logm $ "hsFreeAndDeclaredGhc.details:args=" ++ (showGhc args)
      fds <- mapM pat $ map GHC.unLoc args
      return $ mconcat fds
    details (GHC.RecCon recf) =
      recfields recf
    details (GHC.InfixCon arg1 arg2) = do
      fds <- mapM pat $ map GHC.unLoc [arg1,arg2]
      return $ mconcat fds

    -- Note: this one applies to HsRecFields in LPats
    recfields :: (GHC.HsRecFields GHC.Name (GHC.LPat GHC.Name)) -> RefactGhc (FreeNames,DeclaredNames)
    recfields (GHC.HsRecFields fields _) = do
      let args = map (\(GHC.HsRecField _ (GHC.L _ arg) _) -> arg) fields
      fds <- mapM pat args
      return $ mconcat fds

    -- -----------------------

#if __GLASGOW_HASKELL__ > 704
    bndrs :: GHC.HsWithBndrs (GHC.LHsType GHC.Name) -> RefactGhc (FreeNames,DeclaredNames)
    bndrs (GHC.HsWB (GHC.L _ thing) _kindVars _typeVars) = do
      (_ft,DN dt) <- hsFreeAndDeclaredGhc thing
      -- logm $ "hsFreeAndDeclaredGhc.bndrs (_ft,dt)=" ++ show (_ft,DN dt)
      return (FN dt,DN [])
#endif

    -- -----------------------

    ltydecls :: [GHC.LTyClDecl GHC.Name] -> RefactGhc (FreeNames,DeclaredNames)
    ltydecls ds = do
      fds <- mapM hsFreeAndDeclaredGhc ds
      return $ mconcat fds

    ltydecl :: GHC.LTyClDecl GHC.Name -> RefactGhc (FreeNames,DeclaredNames)
    ltydecl (GHC.L _ (GHC.ForeignType (GHC.L _ n) _)) = return (FN [],DN [n])

    ltydecl (GHC.L _ (GHC.TyFamily _ (GHC.L _ n) _bndrs _)) = return (FN [],DN [n])
#if __GLASGOW_HASKELL__ > 704
    ltydecl (GHC.L _ (GHC.TyDecl (GHC.L _ n) _bndrs _defn fvs))
        = return (FN (GHC.nameSetToList fvs),DN [n])
#else
    ltydecl (GHC.L _ (GHC.TyData _ _ctx (GHC.L _ n) _vars _pats _kind _cons _derivs))
        = return (FN [],DN [n]) -- TODO: calc fvs for cons
    ltydecl (GHC.L _ (GHC.TySynonym (GHC.L _ n) _vars _pats _rhs))
        = return (FN [],DN [n]) -- TODO fvs?
#endif
#if __GLASGOW_HASKELL__ > 704
    ltydecl (GHC.L _ (GHC.ClassDecl _ctx (GHC.L _ n) _tyvars
                     _fds _sigs meths ats atds _docs fvs)) = do
#else
    ltydecl (GHC.L _ (GHC.ClassDecl _ctx (GHC.L _ n) _tyvars
                     _fds _sigs meths ats atds _docs)) = do
#endif
       (_,md) <- hsFreeAndDeclaredGhc meths
       (_,ad) <- hsFreeAndDeclaredGhc ats
       (_,atd) <- hsFreeAndDeclaredGhc atds
#if __GLASGOW_HASKELL__ > 704
       return (FN (GHC.nameSetToList fvs),DN [n] <> md <> ad <> atd)
#else
       return (FN [],DN [n] <> md <> ad <> atd) -- TODO: fvs
#endif

#if __GLASGOW_HASKELL__ > 704
    lfaminstdecls :: [GHC.LFamInstDecl GHC.Name] -> RefactGhc (FreeNames,DeclaredNames)
    lfaminstdecls ds = do
      fds <- mapM hsFreeAndDeclaredGhc ds
      return $ mconcat fds
#endif

#if __GLASGOW_HASKELL__ > 704
    lfaminstdecl :: GHC.LFamInstDecl GHC.Name -> RefactGhc (FreeNames,DeclaredNames)
    lfaminstdecl _f@(GHC.L _ (GHC.FamInstDecl (GHC.L _ n) _pats _defn fvs)) = do
      -- logm $ "hsFreeAndDeclaredGhc.lfaminstdecl:" ++ showGhc _f
      return (FN (GHC.nameSetToList fvs), DN [n])
#else
    -- lfaminstdecl (GHC.L _ (GHC.InstDecl typ binds sigs decls))
#endif

    -- -----------------------

    lsigs :: [GHC.LSig GHC.Name] -> RefactGhc (FreeNames,DeclaredNames)
    lsigs ss = do
      fds <- mapM hsFreeAndDeclaredGhc ss
      return $ mconcat fds

    -- -----------------------

    lsig :: GHC.LSig GHC.Name -> RefactGhc (FreeNames,DeclaredNames)
    lsig (GHC.L _ (GHC.TypeSig ns typ)) = do
      tfds <- hsFreeAndDeclaredGhc typ
      return $ (FN [],DN (map GHC.unLoc ns)) <> tfds
    lsig (GHC.L _ (GHC.GenericSig n typ)) = do
      tfds <- hsFreeAndDeclaredGhc typ
      return $ (FN [],DN (map GHC.unLoc n)) <> tfds
    lsig (GHC.L _ (GHC.IdSig _)) = return emptyFD
    lsig (GHC.L _ (GHC.InlineSig _ _)) = return emptyFD
    lsig (GHC.L _ (GHC.SpecSig n typ _)) = do
      tfds <- hsFreeAndDeclaredGhc typ
      return $ (FN [],DN [GHC.unLoc n]) <> tfds
    lsig (GHC.L _ (GHC.SpecInstSig _)) = return emptyFD
    lsig (GHC.L _ (GHC.FixSig _)) = return emptyFD

    -- -----------------------

    lexprs :: [GHC.LHsExpr GHC.Name] -> RefactGhc (FreeNames,DeclaredNames)
    lexprs es = recurseList es

    -- -----------------------

    lexpr :: GHC.LHsExpr GHC.Name -> RefactGhc (FreeNames,DeclaredNames)
    lexpr (GHC.L _ e) = hsFreeAndDeclaredGhc e

    -- -----------------------

    expr :: GHC.HsExpr GHC.Name -> RefactGhc (FreeNames,DeclaredNames)
    expr ((GHC.HsVar n)) = return (FN [n],DN [])

    expr ((GHC.HsIPVar _)) = return emptyFD

    expr ((GHC.HsOverLit _)) = return emptyFD

    expr ((GHC.HsLit _)) = return emptyFD

    expr ((GHC.HsLam mg)) = hsFreeAndDeclaredGhc mg

#if __GLASGOW_HASKELL__ > 704
    expr ((GHC.HsLamCase _ mg)) = hsFreeAndDeclaredGhc mg
#endif

    expr ((GHC.HsApp e1 e2)) = do
      fde1 <- hsFreeAndDeclaredGhc e1
      fde2 <- hsFreeAndDeclaredGhc e2
      return $ fde1 <> fde2

    expr ((GHC.OpApp e1 eop _fix e2)) = do
      fde1 <- hsFreeAndDeclaredGhc e1
      fdeop <- hsFreeAndDeclaredGhc eop
      fde2 <- hsFreeAndDeclaredGhc e2
      return $ fde1 <> fdeop <> fde2

    expr ((GHC.NegApp e _)) = hsFreeAndDeclaredGhc e

    expr ((GHC.HsPar e)) = hsFreeAndDeclaredGhc e

    expr ((GHC.SectionL e1 e2)) = do
      fde1 <- hsFreeAndDeclaredGhc e1
      fde2 <- hsFreeAndDeclaredGhc e2
      return $ fde1 <> fde2

    expr ((GHC.SectionR e1 e2)) = do
      fde1 <- hsFreeAndDeclaredGhc e1
      fde2 <- hsFreeAndDeclaredGhc e2
      return $ fde1 <> fde2

    expr ((GHC.ExplicitTuple args _boxity)) = do
      let argse = concatMap bb args
          bb (GHC.Missing _) = []
          bb (GHC.Present a) = [a]

      fds <- mapM hsFreeAndDeclaredGhc argse
      return $ mconcat fds

    expr ((GHC.HsCase e body)) = do
       fdes <- hsFreeAndDeclaredGhc e
       fdbs <- hsFreeAndDeclaredGhc body
       return $ fdes <> fdbs

    expr ((GHC.HsIf _ms e1 e2 e3)) = do
      fde1 <- hsFreeAndDeclaredGhc e1
      fde2 <- hsFreeAndDeclaredGhc e2
      fde3 <- hsFreeAndDeclaredGhc e3
      return $ fde1 <> fde2 <> fde3

#if __GLASGOW_HASKELL__ > 704
    expr ((GHC.HsMultiIf _typ rhs))
      = hsFreeAndDeclaredGhc rhs
#endif

    expr ((GHC.HsLet binds e)) = do
      fdb <- hsFreeAndDeclaredGhc binds
      fde <- hsFreeAndDeclaredGhc e
      return $ fdb <> fde

    expr ((GHC.HsDo _ctx stmts _typ))
      = hsFreeAndDeclaredGhc stmts

    expr ((GHC.ExplicitList _typ es))
      = hsFreeAndDeclaredGhc es

    expr ((GHC.ExplicitPArr _typ es))
      = hsFreeAndDeclaredGhc es

    expr ((GHC.RecordCon (GHC.L _ n) _typ binds)) = do
      fdb <- hsFreeAndDeclaredGhc binds
      return $ (FN [],DN [n]) <> fdb

    expr ((GHC.RecordUpd e1 binds _cons _typ1 _typ2)) = do
      fde <- hsFreeAndDeclaredGhc e1
      fdb <- hsFreeAndDeclaredGhc binds
      return $ fde <> fdb

    expr ((GHC.ExprWithTySig e _typ))
      = hsFreeAndDeclaredGhc e

    expr ((GHC.ExprWithTySigOut e _typ))
      = hsFreeAndDeclaredGhc e

    expr ((GHC.ArithSeq _typ as)) = do
      fds <- case as of
        GHC.From e -> hsFreeAndDeclaredGhc e
        GHC.FromThen e1 e2      -> recurseList [e1,e2]
        GHC.FromTo e1 e2        -> recurseList [e1,e2]
        GHC.FromThenTo e1 e2 e3 -> recurseList [e1,e2,e3]
      return fds

    expr ((GHC.PArrSeq _typ as))
      = hsFreeAndDeclaredGhc as

    expr ((GHC.HsSCC _ e))
      = hsFreeAndDeclaredGhc e

    expr ((GHC.HsCoreAnn _ e))
      = hsFreeAndDeclaredGhc e

    expr ((GHC.HsBracket (GHC.ExpBr b)))
      = hsFreeAndDeclaredGhc b
    expr ((GHC.HsBracket (GHC.PatBr b)))
      = hsFreeAndDeclaredGhc b
    expr ((GHC.HsBracket (GHC.DecBrL b)))
      = hsFreeAndDeclaredGhc b
    expr ((GHC.HsBracket (GHC.DecBrG b)))
      = hsFreeAndDeclaredGhc b
    expr ((GHC.HsBracket (GHC.TypBr b)))
      = hsFreeAndDeclaredGhc b
    expr ((GHC.HsBracket (GHC.VarBr _ n)))
      = return (FN [],DN [n])


    expr ((GHC.HsBracketOut b _ps))
      = hsFreeAndDeclaredGhc b

    expr ((GHC.HsSpliceE (GHC.HsSplice _ e)))
      = hsFreeAndDeclaredGhc e

    expr ((GHC.HsQuasiQuoteE _q))
      = return emptyFD

    expr ((GHC.HsProc pa cmd)) = do
      fdp <- hsFreeAndDeclaredGhc pa
      fdc <- hsFreeAndDeclaredGhc cmd
      return $ fdp <> fdc

    expr ((GHC.HsArrApp e1 e2 _typ _atyp _)) = do
      fd1 <- hsFreeAndDeclaredGhc e1
      fd2 <- hsFreeAndDeclaredGhc e2
      return $ fd1 <> fd2

    expr ((GHC.HsArrForm e1 _fix cmds)) = do
      fd1 <- hsFreeAndDeclaredGhc e1
      fdc <- hsFreeAndDeclaredGhc cmds
      return $ fd1 <> fdc

    expr ((GHC.HsTick _ e))
      = hsFreeAndDeclaredGhc e

    expr ((GHC.HsBinTick _ _ e))
      = hsFreeAndDeclaredGhc e

    expr ((GHC.HsTickPragma _ e))
      = hsFreeAndDeclaredGhc e

    expr ((GHC.EWildPat)) = return emptyFD

    expr ((GHC.EAsPat (GHC.L _ n) e)) = do
      fde <- hsFreeAndDeclaredGhc e
      return $ (FN [],DN [n]) <> fde

    expr ((GHC.EViewPat e1 e2)) = do
      fd1 <- hsFreeAndDeclaredGhc e1
      fd2 <- hsFreeAndDeclaredGhc e2
      return $ fd1 <> fd2

    expr ((GHC.ELazyPat e))
      = hsFreeAndDeclaredGhc e

    expr ((GHC.HsType typ))
      = hsFreeAndDeclaredGhc typ

    expr ((GHC.HsWrap _wrap e))
      = hsFreeAndDeclaredGhc e

    -- -----------------------

    name :: GHC.Name -> RefactGhc (FreeNames,DeclaredNames)
    name n = return (FN [],DN [n])

    -- -----------------------
    lstmts :: [GHC.LStmt GHC.Name] -> RefactGhc (FreeNames,DeclaredNames)
    lstmts ss = recurseList ss


    lstmt :: GHC.LStmt GHC.Name -> RefactGhc (FreeNames,DeclaredNames)
    lstmt (GHC.L _ (GHC.LastStmt e _)) = hsFreeAndDeclaredGhc e
    lstmt (GHC.L _ (GHC.BindStmt pa e _ _)) = do
      fdp <- hsFreeAndDeclaredGhc pa
      fde <- hsFreeAndDeclaredGhc e
      return (fdp <> fde)
    lstmt (GHC.L _ (GHC.ExprStmt e _ _ _)) = hsFreeAndDeclaredGhc e
    lstmt (GHC.L _ (GHC.LetStmt bs)) = hsFreeAndDeclaredGhc bs
#if __GLASGOW_HASKELL__ > 704
    lstmt (GHC.L _ (GHC.ParStmt ps _ _)) = hsFreeAndDeclaredGhc ps
#else
    lstmt (GHC.L _ (GHC.ParStmt ps _ _ _)) = hsFreeAndDeclaredGhc ps
#endif
    lstmt (GHC.L _ (GHC.TransStmt _ stmts _ using mby _ _ _)) = do
      fds <- hsFreeAndDeclaredGhc stmts
      fdu <- hsFreeAndDeclaredGhc using
      fdb <- case mby of
        Nothing -> return emptyFD
        Just e -> hsFreeAndDeclaredGhc e
      return $ fds <> fdu <> fdb
    lstmt (GHC.L _ (GHC.RecStmt stmts _ _ _ _ _ _ _ _)) = hsFreeAndDeclaredGhc stmts

    -- -----------------------

    lhstype :: GHC.LHsType GHC.Name -> RefactGhc (FreeNames,DeclaredNames)
    lhstype (GHC.L _ typ) = hstype typ

    -- -----------------------

    hstype :: GHC.HsType GHC.Name -> RefactGhc (FreeNames,DeclaredNames)
    hstype (GHC.HsForAllTy _ _ _ typ) = hsFreeAndDeclaredGhc typ
    hstype (GHC.HsTyVar n) = return (FN [],DN [n])
    hstype (GHC.HsAppTy t1 t2) = recurseList [t1,t2]
    hstype (GHC.HsFunTy t1 t2) = recurseList [t1,t2]
    hstype (GHC.HsListTy typ) = hsFreeAndDeclaredGhc typ
    hstype (GHC.HsPArrTy typ) = hsFreeAndDeclaredGhc typ
    hstype (GHC.HsTupleTy _ typs) = recurseList typs
    hstype (GHC.HsOpTy t1 _ t2) = recurseList [t1,t2]
    hstype (GHC.HsParTy typ) = hsFreeAndDeclaredGhc typ
    hstype (GHC.HsIParamTy _ typ) = hsFreeAndDeclaredGhc typ
    hstype (GHC.HsEqTy t1 t2) = recurseList [t1,t2]
    hstype (GHC.HsKindSig t1 t2) = recurseList [t1,t2]
    hstype (GHC.HsQuasiQuoteTy _) = return emptyFD
    hstype (GHC.HsSpliceTy _ fvs _) = return (FN (GHC.nameSetToList fvs),DN [])
    hstype (GHC.HsDocTy _ typ) = hsFreeAndDeclaredGhc typ
    hstype (GHC.HsBangTy _ typ) = hsFreeAndDeclaredGhc typ
    hstype (GHC.HsRecTy cons) = recurseList cons
    hstype (GHC.HsCoreTy _) = return emptyFD
    hstype (GHC.HsExplicitListTy _ typs) = recurseList typs
    hstype (GHC.HsExplicitTupleTy _ typs) = recurseList typs
#if __GLASGOW_HASKELL__ > 704
    hstype (GHC.HsTyLit _) = return emptyFD
#endif
    hstype (GHC.HsWrapTy _ typ) = hsFreeAndDeclaredGhc typ


    -- -----------------------

    grhs_s :: [GHC.LGRHS GHC.Name] -> RefactGhc (FreeNames,DeclaredNames)
    grhs_s gs = recurseList gs

    -- -----------------------

    grhs :: GHC.LGRHS GHC.Name -> RefactGhc (FreeNames,DeclaredNames)
    grhs (GHC.L _ (GHC.GRHS stmts e)) = do
      fds <- hsFreeAndDeclaredGhc stmts
      fde <- hsFreeAndDeclaredGhc e
      return $ fds <> fde

    -- -----------------------

    grhsss :: [GHC.GRHSs GHC.Name] -> RefactGhc (FreeNames,DeclaredNames)
    grhsss gs = recurseList gs

    -- -----------------------

    grhss :: GHC.GRHSs GHC.Name -> RefactGhc (FreeNames,DeclaredNames)
    grhss (GHC.GRHSs g binds) = do
      (fg,_dg) <- hsFreeAndDeclaredGhc g
      fdb <- hsFreeAndDeclaredGhc binds
      return $  (fg,DN[]) <> fdb

    -- -----------------------

    matchgroup :: GHC.MatchGroup GHC.Name -> RefactGhc (FreeNames,DeclaredNames)
    matchgroup (GHC.MatchGroup matches _) = recurseList matches

    -- -----------------------

    lmatches :: [GHC.LMatch GHC.Name] -> RefactGhc (FreeNames,DeclaredNames)
    lmatches ms = recurseList ms

    -- -----------------------

    lmatch :: GHC.LMatch GHC.Name -> RefactGhc (FreeNames,DeclaredNames)
    lmatch (GHC.L _ _m@(GHC.Match pats _ rhs)) = do
      (fp,DN dp) <- recurseList pats
      (FN fr,DN dr) <- hsFreeAndDeclaredGhc rhs
      let r = (fp,DN []) <> (FN (fr \\ (dr ++ dp)), DN [])
      return $ r

    -- -----------------------

    hsrecordbinds :: (GHC.HsRecordBinds GHC.Name) -> RefactGhc (FreeNames,DeclaredNames)
    hsrecordbinds (GHC.HsRecFields fields _) = recurseList fields

    hsrecordbind :: (GHC.HsRecField GHC.Name (GHC.LHsExpr GHC.Name)) -> RefactGhc (FreeNames,DeclaredNames)
    hsrecordbind (GHC.HsRecField (GHC.L _ n) arg _) = do
      fda <- hsFreeAndDeclaredGhc arg
      return $ (FN [n],DN []) <> fda

    -- -----------------------


    err = error $ "hsFreeAndDeclaredGhc:not matched:" ++ (SYB.showData SYB.Renamer 0 t)

    -- ---------------------------------

    recurseList xs = do
      fds <- mapM hsFreeAndDeclaredGhc xs
      return $ mconcat fds

-- ---------------------------------------------------------------------

-- | Given a RenamedSource LPAT, return the equivalent
-- ParsedSource part.
-- NOTE: returns pristine ParsedSource, since HaRe does not change it
getParsedForRenamedLPat :: GHC.ParsedSource -> GHC.LPat GHC.Name -> GHC.LPat GHC.RdrName
getParsedForRenamedLPat parsed lpatParam@(GHC.L l _pat) = r
  where
    mres = res parsed
    r = case mres of
      Just rr -> rr
      Nothing -> error $ "HaRe error: could not find Parsed LPat for"
                 ++ (SYB.showData SYB.Renamer 0 lpatParam)

    res t = somethingStaged SYB.Parser Nothing (Nothing `SYB.mkQ` lpat) t

    lpat :: (GHC.LPat GHC.RdrName) -> (Maybe (GHC.LPat GHC.RdrName))
    lpat p@(GHC.L lp _)
       | lp == l ||
         stripForestLineFromGhc lp == stripForestLineFromGhc l  = Just p
    lpat _ = Nothing

-- ---------------------------------------------------------------------

-- | Given a RenamedSource Located name, return the equivalent
-- ParsedSource part.
-- NOTE: returns pristine ParsedSource, since HaRe does not change it
getParsedForRenamedLocated :: ({- SYB.Typeable a, SYB.Data a, -} SYB.Typeable b {- , SYB.Data b -})
  => GHC.Located a -> RefactGhc (GHC.Located b)
getParsedForRenamedLocated (GHC.L l _n) = do
  parsed <- getRefactParsed
  let
    mres = res parsed
    r = case mres of
      Just rr -> rr
      Nothing -> error $ "HaRe error: could not find Parsed Location for"
                 ++ (showGhc l)

    res t = somethingStaged SYB.Parser Nothing (Nothing `SYB.mkQ` lname) t

    lname :: (GHC.Located b) -> (Maybe (GHC.Located b))
    lname p@(GHC.L lp _)
       | lp == l ||
         stripForestLineFromGhc lp == stripForestLineFromGhc l  = Just p
    lname _ = Nothing

  return r


-- | Given a RenamedSource Located name, return the equivalent
-- ParsedSource part.
-- NOTE: returns pristine ParsedSource, since HaRe does not change it
getParsedForRenamedName :: GHC.ParsedSource -> GHC.Located GHC.Name -> GHC.Located GHC.RdrName
getParsedForRenamedName parsed n@(GHC.L l _n) = r
  where
    mres = res parsed
    r = case mres of
      Just rr -> rr
      Nothing -> error $ "HaRe error: could not find Parsed LPat for"
                 ++ (SYB.showData SYB.Renamer 0 n)

    res t = somethingStaged SYB.Parser Nothing (Nothing `SYB.mkQ` lname) t

    lname :: (GHC.Located GHC.RdrName) -> (Maybe (GHC.Located GHC.RdrName))
    lname p@(GHC.L lp _)
       | lp == l ||
         stripForestLineFromGhc lp == stripForestLineFromGhc l  = Just p
    lname _ = Nothing

-- ---------------------------------------------------------------------

getDeclaredTypes :: GHC.LTyClDecl GHC.Name -> [GHC.Name]
getDeclaredTypes (GHC.L _ (GHC.ForeignType (GHC.L _ n) _)) = [n]
getDeclaredTypes (GHC.L _ (GHC.TyFamily _ (GHC.L _ n) _bs _)) = [n]
#if __GLASGOW_HASKELL__ > 704
getDeclaredTypes (GHC.L _ (GHC.TyDecl (GHC.L _ n) _vars defn _fvs)) = nub $ [n] ++ dsn
  where
    dsn = getHsTyDefn defn
#else
-- data,
getDeclaredTypes (GHC.L _ (GHC.TyData _ _ctx (GHC.L _ n) _vars _pats _kind cons _derivs))
  = nub $ [n] ++ cs
  where
    getConDecl (GHC.L _ (GHC.ConDecl (GHC.L _ n2) _ _ _ _ _ _ _)) = n2
    cs = map getConDecl cons
-- synonym
getDeclaredTypes (GHC.L _ (GHC.TySynonym (GHC.L _ n) _vars _pats _rhs)) = [n]
#endif
#if __GLASGOW_HASKELL__ > 704
getDeclaredTypes (GHC.L _ (GHC.ClassDecl _ (GHC.L _ n) _vars _fds sigs meths ats _atdefs _ _fvs))
#else
getDeclaredTypes (GHC.L _ (GHC.ClassDecl _ (GHC.L _ n) _vars _fds sigs meths ats _atdefs _))
#endif
  = nub $ [n] ++ ssn ++ msn ++ asn
  where
    getLSig :: GHC.LSig GHC.Name -> [GHC.Name]
    getLSig (GHC.L _ (GHC.TypeSig ns _)) = map GHC.unLoc ns
    getLSig (GHC.L _ (GHC.GenericSig ns _)) = map GHC.unLoc ns
    getLSig (GHC.L _ (GHC.IdSig _n)) = []
    getLSig (GHC.L _ (GHC.InlineSig (GHC.L _ n2) _)) = [n2]
    getLSig (GHC.L _ (GHC.SpecSig (GHC.L _ n2) _ _)) = [n2]
    getLSig (GHC.L _ (GHC.SpecInstSig _)) = []
    getLSig (GHC.L _ (GHC.FixSig _)) = []

    ssn = concatMap getLSig sigs
    msn = getDeclaredVars $ hsBinds meths
    asn = concatMap getDeclaredTypes ats

-- -------------------------------------

#if __GLASGOW_HASKELL__ > 704
getHsTyDefn :: GHC.HsTyDefn GHC.Name -> [GHC.Name]
getHsTyDefn (GHC.TySynonym _) = []
getHsTyDefn (GHC.TyData _ _  _ _ cons _) = r
  where
    getConDecl (GHC.L _ (GHC.ConDecl (GHC.L _ n) _ _ _ _ _ _ _)) = n
    r = map getConDecl cons
#endif

-- ---------------------------------------------------------------------
-- |Experiment with GHC fvs stuff
getFvs :: [GHC.LHsBind GHC.Name] -> [([GHC.Name], GHC.NameSet)]
getFvs bs = concatMap binds bs
  where
      binds :: (GHC.LHsBind GHC.Name) -> [([GHC.Name],GHC.NameSet)]
      binds (GHC.L _ (GHC.FunBind (GHC.L _ pname) _ _ _ fvs _)) = [([pname],     fvs)]
      binds (GHC.L _ (GHC.PatBind p _rhs _ty fvs _))            = [((hsNamess p),fvs)]
      binds _ = []

getFreeVars :: [GHC.LHsBind GHC.Name] -> [GHC.Name]
getFreeVars bs = concatMap binds bs
  where
      binds :: (GHC.LHsBind GHC.Name) -> [GHC.Name]
      binds (GHC.L _ (GHC.FunBind (GHC.L _ _pname) _ _ _ fvs _)) = (GHC.nameSetToList fvs)
      binds (GHC.L _ (GHC.PatBind _p _rhs _ty fvs _))            = (GHC.nameSetToList fvs)
      binds _ = []

getDeclaredVars :: [GHC.LHsBind GHC.Name] -> [GHC.Name]
getDeclaredVars bs = concatMap vars bs
  where
      vars :: (GHC.LHsBind GHC.Name) -> [GHC.Name]
      vars (GHC.L _ (GHC.FunBind (GHC.L _ pname) _ _ _ _fvs _)) = [pname]
      vars (GHC.L _ (GHC.PatBind p _rhs _ty _fvs _))            = (hsNamess p)
      vars _ = []

--------------------------------------------------------------------------------
-- | Same as `hsVisiblePNs' except that the returned identifiers are
-- in String format.
hsVisibleNames:: (FindEntity t1, SYB.Data t1, SYB.Data t2,HsValBinds t2,GHC.Outputable t1)
  => t1 -> t2 -> RefactGhc [String]
hsVisibleNames e t = do
    d <- hsVisiblePNs e t
    return ((nub . map showGhc) d)

------------------------------------------------------------------------

-- | Given syntax phrases e and t, if e occurs in t, then return those
-- variables which are declared in t and accessible to e, otherwise
-- return [].
hsVisiblePNs :: (FindEntity e, SYB.Data e, SYB.Data t,HsValBinds t,GHC.Outputable e)
             => e -> t -> RefactGhc [GHC.Name]
hsVisiblePNs e t = do
  (DN dn) <- hsVisibleDs e t
  return dn

------------------------------------------------------------------------

-- | Given syntax phrases e and t, if e occurs in t, then return those
-- variables which are declared in t and accessible to e, otherwise
-- return [].
hsVisibleDs :: (FindEntity e, SYB.Data e, SYB.Data t,HsValBinds t,GHC.Outputable e)
             => e -> t -> RefactGhc DeclaredNames
hsVisibleDs e t = do
  -- logm $ "hsVisibleDs:(e,t)=" ++ (SYB.showData SYB.Renamer 0 (e,t))
  (DN d) <- res
  return (DN (nub d))
  where
    -- TODO: this is effectively a recursive descent approach, where
    --       each syntax element processor knows exactly what it needs
    --       in terms of sub-elements. Hence as an optimisation,
    --       consider calling the relevent element directly, instead
    --       of looping back into the main function.
    res = (const err -- (DN [])
          `SYB.extQ` renamed
          `SYB.extQ` valbinds
          `SYB.extQ` lhsbindslr
          `SYB.extQ` hsbinds
          `SYB.extQ` hsbind
          `SYB.extQ` hslocalbinds
          `SYB.extQ` lmatch
          `SYB.extQ` grhss
          `SYB.extQ` lgrhs
          `SYB.extQ` lexpr
          `SYB.extQ` tycldeclss
          `SYB.extQ` tycldecls
          `SYB.extQ` tycldecl
          `SYB.extQ` instdecls
          `SYB.extQ` instdecl
          `SYB.extQ` lhstype
          `SYB.extQ` lsigs
          `SYB.extQ` lsig
          ) t

    renamed :: GHC.RenamedSource -> RefactGhc DeclaredNames
    renamed (g,_i,_ex,_d)
      | findEntity e g = do
         dfds <- hsVisibleDs e $ GHC.hs_valds g
         tfds <- hsVisibleDs e $ GHC.hs_tyclds g
         ifds <- hsVisibleDs e $ GHC.hs_instds g
         return $ dfds <> tfds <> ifds
    renamed _ = return (DN [])

    valbinds :: (GHC.HsValBindsLR GHC.Name GHC.Name) -> RefactGhc DeclaredNames
    valbinds vb@(GHC.ValBindsIn bindsBag sigs)
      | findEntity e vb = do
          fdsb <- mapM (hsVisibleDs e) $ hsBinds bindsBag
          fdss <- mapM (hsVisibleDs e) sigs
          return $ mconcat fdss <> mconcat fdsb
    valbinds vb@(GHC.ValBindsOut binds sigs)
      | findEntity e vb = do
          logm $ "hsVisibleDs.valbinds:ValBindsOut"
          fdsb <- mapM (hsVisibleDs e) $ map snd binds
          fdss <- mapM (hsVisibleDs e) sigs
          return $ mconcat fdss <> mconcat fdsb

    valbinds _ = do
      logm $ "hsVisibleDs.valbinds:not matched"
      return (DN [])

    lhsbindslr :: GHC.LHsBindsLR GHC.Name GHC.Name -> RefactGhc DeclaredNames
    lhsbindslr bs = do
      fds <- mapM (hsVisibleDs e) $ GHC.bagToList bs
      return $ mconcat fds

    hsbinds :: [GHC.LHsBind GHC.Name] -> RefactGhc DeclaredNames
    hsbinds ds
      | findEntity e ds = do
        fds <- mapM (hsVisibleDs e) ds
        return $ mconcat fds
    hsbinds _ = return (DN [])

    hsbind :: (GHC.LHsBind GHC.Name) -> RefactGhc DeclaredNames
    hsbind ((GHC.L _ (GHC.FunBind _n _ (GHC.MatchGroup matches _) _ _ _)))
      | findEntity e matches = do
          fds <- mapM (hsVisibleDs e) matches
          logm $ "hsVisibleDs.hsbind:fds=" ++ show fds
          return $ mconcat fds
    hsbind _ = return (DN [])

    hslocalbinds :: (GHC.HsLocalBinds GHC.Name) -> RefactGhc DeclaredNames
    hslocalbinds (GHC.HsValBinds binds)
      | findEntity e binds = hsVisibleDs e binds
    hslocalbinds (GHC.HsIPBinds binds)
      | findEntity e binds = hsVisibleDs e binds
    hslocalbinds (GHC.EmptyLocalBinds) = return (DN [])
    hslocalbinds _ = return (DN [])

    lmatch :: (GHC.LMatch GHC.Name) -> RefactGhc DeclaredNames
    lmatch (GHC.L _ (GHC.Match pats _mtyp rhs))
      | findEntity e pats = do
           logm $ "hsVisibleDs.lmatch:in pats="
           return (DN []) -- TODO: extend this
      | findEntity e rhs = do
           ( pf,pd) <- hsFreeAndDeclaredGhc pats
           logm $ "hsVisibleDs.lmatch:(pf,pd)=" ++ (show (pf,pd))
           (    rd) <- hsVisibleDs e rhs
           return (pd <> rd)
    lmatch _ =return  (DN [])

    grhss :: (GHC.GRHSs GHC.Name) -> RefactGhc DeclaredNames
    grhss (GHC.GRHSs guardedRhss lstmts)
      | findEntity e guardedRhss = do
          fds <- mapM (hsVisibleDs e) guardedRhss
          return $ mconcat fds
      | findEntity e lstmts = hsVisibleDs e lstmts
    grhss _ = return (DN [])

    lgrhs :: GHC.LGRHS GHC.Name -> RefactGhc DeclaredNames
    lgrhs (GHC.L _ (GHC.GRHS stmts ex))
      | findEntity e stmts = hsVisibleDs e stmts
      | findEntity e ex    = hsVisibleDs e ex
    lgrhs _ = return (DN [])


    lexpr :: GHC.LHsExpr GHC.Name -> RefactGhc DeclaredNames
    lexpr (GHC.L _ (GHC.HsVar n))
      | findEntity e n  = return (DN [n])
    lexpr (GHC.L _ (GHC.HsLet lbinds expr))
      | findEntity e lbinds || findEntity e expr  = do
        (_,lds) <- hsFreeAndDeclaredGhc lbinds
        (_,eds) <- hsFreeAndDeclaredGhc expr
        return $ lds <> eds

    lexpr expr
      | findEntity e expr = do
        -- logm $ "hsVisibleDs.lexpr.e1:" ++ (showGhc (e1,_eOp,e2))
        (FN efs,_) <- hsFreeAndDeclaredGhc expr
        (FN _eefs,DN eeds) <- hsFreeAndDeclaredGhc e
        -- return (DN e1fs <> DN eofs <> DN e2fs)
        return (DN (efs \\ eeds))

    lexpr _ = return (DN [])


    tycldeclss :: [[GHC.LTyClDecl GHC.Name]] -> RefactGhc DeclaredNames
    tycldeclss tcds
      | findEntity e tcds = do
        fds <- mapM (hsVisibleDs e) tcds
        return $ mconcat fds
    tycldeclss _ = return (DN [])

    tycldecls :: [GHC.LTyClDecl GHC.Name] -> RefactGhc DeclaredNames
    tycldecls tcds
      | findEntity e tcds = do
        fds <- mapM (hsVisibleDs e) tcds
        return $ mconcat fds
    tycldecls _ = return (DN [])

    tycldecl :: GHC.LTyClDecl GHC.Name -> RefactGhc DeclaredNames
    tycldecl tcd
      | findEntity e tcd = do
        (_,ds) <- hsFreeAndDeclaredGhc tcd
        return ds
    tycldecl _ = return (DN [])

    instdecls :: [GHC.LInstDecl GHC.Name] -> RefactGhc DeclaredNames
    instdecls ds
      | findEntity e ds = do
        fds <- mapM (hsVisibleDs e) ds
        return $ mconcat fds
    instdecls _ = return (DN [])

    instdecl :: GHC.LInstDecl GHC.Name -> RefactGhc DeclaredNames
#if __GLASGOW_HASKELL__ > 704
    instdecl (GHC.L _ (GHC.ClsInstD polytyp binds sigs faminsts))
#else
    instdecl (GHC.L _ (GHC.InstDecl polytyp binds sigs faminsts))
#endif
      | findEntity e polytyp  = hsVisibleDs e polytyp
      | findEntity e binds    = hsVisibleDs e binds
      | findEntity e sigs     = hsVisibleDs e sigs
      | findEntity e faminsts = hsVisibleDs e faminsts
    instdecl _ = return (DN [])

    lhstype :: GHC.LHsType GHC.Name -> RefactGhc DeclaredNames
    lhstype tv@(GHC.L _ (GHC.HsTyVar n))
      | findEntity e tv = return (DN [n])
    lhstype _ = return (DN [])

    -- -----------------------

    lsigs :: [GHC.LSig GHC.Name] -> RefactGhc DeclaredNames
    lsigs ss = do
      fds <- mapM (hsVisibleDs e) ss
      return $ mconcat fds

    -- -----------------------

    lsig :: GHC.LSig GHC.Name -> RefactGhc DeclaredNames
    lsig (GHC.L _ (GHC.TypeSig _ns typ))
      | findEntity e typ = hsVisibleDs e typ
    lsig (GHC.L _ (GHC.GenericSig _n typ))
      | findEntity e typ = hsVisibleDs e typ
    lsig (GHC.L _ (GHC.IdSig _)) = return (DN [])
    lsig (GHC.L _ (GHC.InlineSig _ _)) = return (DN [])
    lsig (GHC.L _ (GHC.SpecSig _n typ _))
      | findEntity e typ = hsVisibleDs e typ
    lsig (GHC.L _ (GHC.SpecInstSig _)) = return (DN [])

    lsig _ = return (DN [])

    -- -----------------------
    err = error $ "hsVisibleDs:no match for:" ++ (SYB.showData SYB.Renamer 0 t)


------------------------------------------------------------------------

-- | Return True if the identifier is unqualifiedly used in the given
-- syntax phrase.
-- usedWithoutQualR :: GHC.Name -> GHC.ParsedSource -> Bool
usedWithoutQualR ::  (SYB.Data t) => GHC.Name -> t -> Bool
usedWithoutQualR name parsed = fromMaybe False res
  where
     res = somethingStaged SYB.Parser Nothing
            (Nothing `SYB.mkQ` worker
            `SYB.extQ` workerBind
            `SYB.extQ` workerExpr
            ) parsed

     worker  (pname :: GHC.Located GHC.RdrName) =
       checkName pname

     workerBind (GHC.L l (GHC.VarPat n) :: (GHC.Located (GHC.Pat GHC.RdrName))) =
       checkName (GHC.L l n)
     workerBind _ = Nothing

     workerExpr ((GHC.L l (GHC.HsVar n)) :: (GHC.Located (GHC.HsExpr GHC.RdrName)))
       = checkName (GHC.L l n)
     workerExpr _ = Nothing

     -- ----------------

     checkName ((GHC.L l pn)::GHC.Located GHC.RdrName)
        | ((GHC.rdrNameOcc pn) == (GHC.nameOccName name)) &&
          -- isUsedInRhs pname parsed &&
          isUsedInRhs (GHC.L l name) parsed &&
          GHC.isUnqual pn     = Just True
     checkName _ = Nothing


-- ---------------------------------------------------------------------


-- |`hsFDsFromInside` is different from `hsFreeAndDeclaredPNs` in
-- that: given an syntax phrase t, `hsFDsFromInside` returns not only
-- the declared variables that are visible from outside of t, but also
-- those declared variables that are visible to the main expression
-- inside t.
-- NOTE: Expects to be given RenamedSource
hsFDsFromInside:: (SYB.Data t) => t-> RefactGhc ([GHC.Name],[GHC.Name])
hsFDsFromInside t = do
   r <- hsFDsFromInside' t
   return r
   where
     hsFDsFromInside' :: (SYB.Data t) => t -> RefactGhc ([GHC.Name],[GHC.Name])
     hsFDsFromInside' t1 = do
          r1 <- applyTU (once_tdTU (failTU  `adhocTU` renamed
                                            `adhocTU` decl
                                            `adhocTU` match
                                            `adhocTU` expr
                                            `adhocTU` stmts )) t1
          -- let (f',d') = fromMaybe ([],[]) r1
          let (f',d') = r1
          return (nub f', nub d')

     renamed :: GHC.RenamedSource -> RefactGhc ([GHC.Name],[GHC.Name])
     renamed ((grp,_,_,_)::GHC.RenamedSource)
        = hsFreeAndDeclaredPNs $ GHC.hs_valds grp

     -- Match [LPat id] (Maybe (LHsType id)) (GRHSs id)
     match :: GHC.Match GHC.Name -> RefactGhc ([GHC.Name],[GHC.Name])
     match ((GHC.Match pats _type rhs):: GHC.Match GHC.Name ) = do
       (pf, pd) <- hsFreeAndDeclaredPNs pats
       (rf, rd) <- hsFreeAndDeclaredPNs rhs
       return (nub (pf `union` (rf \\ pd)),
               nub (pd `union` rd))

     -- ----------------------

     decl :: GHC.HsBind GHC.Name -> RefactGhc ([GHC.Name],[GHC.Name])
     decl ((GHC.FunBind (GHC.L _ _) _ (GHC.MatchGroup matches _) _ _ _) :: GHC.HsBind GHC.Name) =
       do
         fds <- mapM hsFDsFromInside' matches
         -- error (show $ nameToString n)
         return (nub (concatMap fst fds), nub (concatMap snd fds))

     decl ((GHC.PatBind p rhs _ _ _) :: GHC.HsBind GHC.Name) =
       do
         (pf, pd) <- hsFreeAndDeclaredPNs p
         (rf, rd) <- hsFreeAndDeclaredPNs rhs
         return
           (nub (pf `union` (rf \\ pd)),
            nub (pd `union` rd))

     decl ((GHC.VarBind p rhs _) :: GHC.HsBind GHC.Name) =
       do
         (pf, pd) <- hsFreeAndDeclaredPNs p
         (rf, rd) <- hsFreeAndDeclaredPNs rhs
         return
           (nub (pf `union` (rf \\ pd)),
            nub (pd `union` rd))

     decl _ = return ([],[])

     -- ----------------------

     expr ((GHC.HsLet decls e) :: GHC.HsExpr GHC.Name) =
       do
         (df,dd) <- hsFreeAndDeclaredPNs decls
         (ef,_)  <- hsFreeAndDeclaredPNs e
         return (nub (df `union` (ef \\ dd)), nub dd)

     expr ((GHC.HsLam (GHC.MatchGroup matches _)) :: GHC.HsExpr GHC.Name) =
       hsFreeAndDeclaredPNs matches

     expr ((GHC.HsCase e (GHC.MatchGroup matches _)) :: GHC.HsExpr GHC.Name) =
       do
         (ef,_)  <- hsFreeAndDeclaredPNs e
         (df,dd) <- hsFreeAndDeclaredPNs matches
         return (nub (df `union` (ef \\ dd)), nub dd)

     -- expr _ = return ([],[])
     expr _ = mzero

     stmts ((GHC.BindStmt pat e1 e2 e3) :: GHC.Stmt GHC.Name) =
       do
         (pf,pd)  <- hsFreeAndDeclaredPNs pat
         (ef,_ed) <- hsFreeAndDeclaredPNs e1
         (df,dd)  <- hsFreeAndDeclaredPNs [e2,e3]
         return
           (nub (pf `union` (((ef \\ dd) `union` df) \\ pd)), nub (pd `union` dd))

     stmts ((GHC.LetStmt binds) :: GHC.Stmt GHC.Name) =
       hsFreeAndDeclaredPNs binds

     -- stmts _ = return ([],[])
     stmts _ = mzero



-- | The same as `hsFDsFromInside` except that the returned variables
-- are in the String format
hsFDNamesFromInside::(SYB.Data t) => t -> RefactGhc ([String],[String])
hsFDNamesFromInside t = do
  (f,d) <- hsFDsFromInside t
  return
    ((nub.map showGhc) f, (nub.map showGhc) d)

-- ---------------------------------------------------------------------
-- | True if the name is a field name
isFieldName :: GHC.Name -> Bool
isFieldName _n = error "undefined isFieldName"

-- ---------------------------------------------------------------------
-- | True if the name is a field name
isClassName :: GHC.Name -> Bool
isClassName _n = error "undefined isClassName"

-- ---------------------------------------------------------------------
-- | True if the name is a class instance
isInstanceName :: GHC.Name -> Bool
isInstanceName _n = error "undefined isInstanceName"


-- ---------------------------------------------------------------------
-- | Collect the identifiers (in PName format) in a given syntax phrase.

hsPNs::(SYB.Data t)=> t -> [PName]
hsPNs t = (nub.ghead "hsPNs") res
  where
     res = SYB.everythingStaged SYB.Parser (++) [] ([] `SYB.mkQ` inPnt) t

     inPnt (pname :: GHC.RdrName) = return [(PN pname)]

-- ---------------------------------------------------------------------

-- |Get all the names in the given syntax element
hsNamess :: (SYB.Data t) => t -> [GHC.Name]
-- hsNamess t = (nub.ghead "hsNamess") res
hsNamess t = nub $ concat res
  where
     res = SYB.everythingStaged SYB.Renamer (++) [] ([] `SYB.mkQ` inName) t

     inName (pname :: GHC.Name) = return [pname]

-----------------------------------------------------------------------------

getModule :: RefactGhc GHC.Module
getModule = do
  typechecked <- getTypecheckedModule
  return $ GHC.ms_mod $ GHC.pm_mod_summary $ GHC.tm_parsed_module typechecked

-- ---------------------------------------------------------------------

-- | Return True if a string is a lexically  valid variable name.
isVarId :: String -> Bool
isVarId mid = isId mid && isSmall (ghead "isVarId" mid)
     where isSmall c=isLower c || c=='_'

-- | Return True if a string is a lexically valid constructor name.
isConId :: String -> Bool
isConId mid = isId mid && isUpper (ghead "isConId" mid)

-- | Return True if a string is a lexically valid operator name.
isOperator :: String->Bool
isOperator mid = mid /= [] && isOpSym (ghead "isOperator" mid) &&
                isLegalOpTail (tail mid) && not (isReservedOp mid)
   where
    isOpSym mid' = elem mid' opSymbols
       where opSymbols = ['!', '#', '$', '%', '&', '*', '+','.','/','<','=','>','?','@','\'','^','|','-','~']

    isLegalOpTail tail' = all isLegal tail'
       where isLegal c = isOpSym c || c==':'

    isReservedOp mid' = elem mid' reservedOps
       where reservedOps = ["..", ":","::","=","\"", "|","<-","@","~","=>"]

-- | Returns True if a string lexically is an identifier.
-- *This function should not be exported.*
isId::String->Bool
isId mid = mid/=[] && isLegalIdTail (tail mid) && not (isReservedId mid)
  where
    isLegalIdTail tail' = all isLegal tail'
        where isLegal c=isSmall c|| isUpper c || isDigit c || c=='\''

    isReservedId mid' = elem mid' reservedIds
      where reservedIds=["case", "class", "data", "default", "deriving","do","else" ,"if",
                         "import", "in", "infix","infixl","infixr","instance","let","module",
                         "newtype", "of","then","type","where","_"]

    isSmall c=isLower c || c=='_'

-----------------------------------------------------------------------------

-- |Return True if a PName is a toplevel PName.
isTopLevelPN::GHC.Name -> RefactGhc Bool
isTopLevelPN n = do
  typechecked <- getTypecheckedModule
  let maybeNames = GHC.modInfoTopLevelScope $ GHC.tm_checked_module_info typechecked
  let names = fromMaybe [] maybeNames
  return $ n `elem` names


-- |Return True if a PName is a local PName.
isLocalPN::GHC.Name -> Bool
isLocalPN = GHC.isInternalName
-- isLocalPN (PN i (UniqueNames.S _)) = True
-- isLocalPN _ = False

-- |Return True if the name has a @GHC.SrcSpan@, i.e. is declared in
-- source we care about
isNonLibraryName :: GHC.Name -> Bool
isNonLibraryName n = case (GHC.nameSrcSpan n) of
  GHC.UnhelpfulSpan _ -> False
  _                   -> True


-- |Return True if a PName is a function\/pattern name defined in t.
isFunOrPatName::(SYB.Data t) => GHC.Name -> t -> Bool
isFunOrPatName pn
   =isJust.somethingStaged SYB.Parser Nothing (Nothing `SYB.mkQ` worker)
     where
        -- worker (decl::HsDeclP)
        worker (decl::GHC.LHsBind GHC.Name)
           | defines pn decl = Just True
        worker _ = Nothing

-------------------------------------------------------------------------------
-- |Return True if a PName is a qualified PName.
--  AZ:NOTE: this tests the use instance, the underlying name may be qualified.
--           e.g. used name is zip, GHC.List.zip
--     NOTE2: not sure if this gives a meaningful result for a GHC.Name
isQualifiedPN :: GHC.Name -> RefactGhc Bool
isQualifiedPN name = return $ GHC.isQual $ GHC.nameRdrName name


-- | Return True if a declaration is a type signature declaration.
isTypeSig :: GHC.Located (GHC.Sig a) -> Bool
isTypeSig (GHC.L _ (GHC.TypeSig _ _)) = True
isTypeSig _ = False

-- | Return True if a declaration is a function definition.
isFunBindP::HsDeclP -> Bool
isFunBindP (GHC.L _ (GHC.ValD (GHC.FunBind _ _ _ _ _ _))) = True
isFunBindP _ =False

isFunBindR::GHC.LHsBind t -> Bool
isFunBindR (GHC.L _l (GHC.FunBind _ _ _ _ _ _)) = True
isFunBindR _ =False

-- | Returns True if a declaration is a pattern binding.
isPatBindP::HsDeclP->Bool
isPatBindP (GHC.L _ (GHC.ValD (GHC.PatBind _ _ _ _ _))) = True
isPatBindP _=False

isPatBindR::GHC.LHsBind t -> Bool
isPatBindR (GHC.L _ (GHC.PatBind _ _ _ _ _)) = True
isPatBindR _=False


-- | Return True if a declaration is a pattern binding which only
-- defines a variable value.
isSimplePatBind :: (SYB.Data t) => GHC.LHsBind t-> Bool
isSimplePatBind decl = case decl of
     (GHC.L _l (GHC.PatBind p _rhs _ty _fvs _)) -> hsPNs p /= []
     _ -> False

-- | Return True if a declaration is a pattern binding but not a simple one.
isComplexPatBind::GHC.LHsBind GHC.Name -> Bool
isComplexPatBind decl = case decl of
     (GHC.L _l (GHC.PatBind p _rhs _ty _fvs _)) -> patToPNT p /= Nothing
     _ -> False

-- | Return True if a declaration is a function\/pattern definition.
isFunOrPatBindP::HsDeclP->Bool
isFunOrPatBindP decl = isFunBindP decl || isPatBindP decl

-- | Return True if a declaration is a function\/pattern definition.
isFunOrPatBindR::GHC.LHsBind t -> Bool
isFunOrPatBindR decl = isFunBindR decl || isPatBindR decl

-------------------------------------------------------------------------------
{-
getValBindSigs :: GHC.HsValBinds GHC.Name -> [GHC.LSig GHC.Name]
getValBindSigs binds = case binds of
    GHC.ValBindsIn  _ sigs -> sigs
    GHC.ValBindsOut _ sigs -> sigs

emptyValBinds :: GHC.HsValBinds GHC.Name
emptyValBinds = GHC.ValBindsIn (GHC.listToBag []) []

unionBinds :: [GHC.HsValBinds GHC.Name] ->  GHC.HsValBinds GHC.Name
unionBinds [] = emptyValBinds
unionBinds [x] = x
unionBinds (x1:x2:xs) = unionBinds ((mergeBinds x1 x2):xs)
  where
    mergeBinds :: GHC.HsValBinds GHC.Name -> GHC.HsValBinds GHC.Name -> GHC.HsValBinds GHC.Name
    mergeBinds (GHC.ValBindsIn b1 s1) (GHC.ValBindsIn b2 s2) = (GHC.ValBindsIn (GHC.unionBags b1 b2) (s1++s2))
    mergeBinds (GHC.ValBindsOut b1 s1) (GHC.ValBindsOut b2 s2) = (GHC.ValBindsOut (b1++b2) (s1++s2))
    mergeBinds y1@(GHC.ValBindsIn _ _) y2@(GHC.ValBindsOut _  _) = mergeBinds y2 y1
    mergeBinds    (GHC.ValBindsOut b1 s1) (GHC.ValBindsIn b2 s2) = (GHC.ValBindsOut (b1++[(GHC.NonRecursive,b2)]) (s1++s2))
-}

-- NOTE: ValBindsIn are found before the Renamer, ValBindsOut after
{-
hsBinds :: (HsValBinds t) => t -> [GHC.LHsBind GHC.Name]
hsBinds t = case hsValBinds t of
  GHC.ValBindsIn binds _sigs -> GHC.bagToList binds
  GHC.ValBindsOut bs _sigs -> concatMap (\(_,b) -> GHC.bagToList b) bs

replaceBinds :: (HsValBinds t) => t -> [GHC.LHsBind GHC.Name] -> t
-- replaceBinds t bs = replaceValBinds t (GHC.ValBindsIn (GHC.listToBag bs) [])
replaceBinds t bs = replaceValBinds t (GHC.ValBindsIn (GHC.listToBag bs) sigs)
  where
    sigs = case hsValBinds t of
      GHC.ValBindsIn  _ s -> s
      GHC.ValBindsOut _ s -> s
-}
{-
-- This class replaces the HsDecls one
class (SYB.Data t) => HsValBinds t where

    -- | Return the binds that are directly enclosed in the
    -- given syntax phrase.
    -- hsValBinds :: t -> [GHC.LHsBind GHC.Name]
    hsValBinds :: t -> GHC.HsValBinds GHC.Name

    -- | Replace the directly enclosed bind list by the given
    --  bind list. Note: This function does not modify the
    --  token stream.
    -- replaceBinds :: t -> [GHC.LHsBind GHC.Name] -> t
    replaceValBinds :: t -> GHC.HsValBinds GHC.Name -> t

    -- | Return True if the specified identifier is declared in the
    -- given syntax phrase.
    -- isDeclaredIn :: GHC.Name -> t -> Bool

    -- | Return the type class definitions that are directly enclosed
    -- in the given syntax phrase. Note: only makes sense for
    -- GHC.RenamedSource
    hsTyDecls :: t -> [[GHC.LTyClDecl GHC.Name]]
-}
-- ++AZ++ see if we can get away with one only..
isDeclaredIn :: (HsValBinds t) => GHC.Name -> t -> Bool
isDeclaredIn name t = nonEmptyList $ definingDeclsNames [name] (hsBinds t) False True

{-
instance HsValBinds (GHC.RenamedSource) where
  hsValBinds (grp,_,_,_) = (GHC.hs_valds grp)

  replaceValBinds (grp,imps,exps,docs) binds = (grp',imps,exps,docs)
    where
      grp' = grp {GHC.hs_valds = binds}

  hsTyDecls (grp,_,_,_) = (GHC.hs_tyclds grp)


instance HsValBinds (GHC.HsValBinds GHC.Name) where
  hsValBinds vb = vb
  replaceValBinds _old new = new
  hsTyDecls _ = []

instance HsValBinds (GHC.HsGroup GHC.Name) where
  hsValBinds grp = (GHC.hs_valds grp)

  replaceValBinds (GHC.HsGroup b t i d f de fo w a r v doc) binds
    = (GHC.HsGroup b' t i d f de fo w a r v doc)
       where b' = replaceValBinds b binds

  hsTyDecls _ = []

instance HsValBinds (GHC.HsLocalBinds GHC.Name) where
  hsValBinds lb = case lb of
    GHC.HsValBinds b    -> b
    GHC.HsIPBinds _     -> emptyValBinds
    GHC.EmptyLocalBinds -> emptyValBinds

  replaceValBinds (GHC.HsValBinds _b) new    = (GHC.HsValBinds new)
  replaceValBinds (GHC.HsIPBinds _b) _new    = error "undefined replaceValBinds HsIPBinds"
  replaceValBinds (GHC.EmptyLocalBinds) new  = (GHC.HsValBinds new)

  hsTyDecls _ = []

instance HsValBinds (GHC.GRHSs GHC.Name) where
  hsValBinds (GHC.GRHSs _ lb) = hsValBinds lb

  replaceValBinds (GHC.GRHSs rhss b) new = (GHC.GRHSs rhss (replaceValBinds b new))

  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds (GHC.MatchGroup GHC.Name) where
  hsValBinds (GHC.MatchGroup matches _) = hsValBinds matches

  replaceValBinds (GHC.MatchGroup matches a) newBinds
               = (GHC.MatchGroup (replaceValBinds matches newBinds) a)

  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds [GHC.LMatch GHC.Name] where
  hsValBinds ms = unionBinds $ map (\m -> hsValBinds $ GHC.unLoc m) ms

  replaceValBinds [] _        = error "empty match list in replaceValBinds [GHC.LMatch GHC.Name]"
  replaceValBinds ms newBinds = (replaceValBinds (ghead "replaceValBinds" ms) newBinds):(tail ms)

  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds (GHC.LMatch GHC.Name) where
  hsValBinds m = hsValBinds $ GHC.unLoc m

  replaceValBinds (GHC.L l m) newBinds = (GHC.L l (replaceValBinds m newBinds))

  hsTyDecls _ = []

-- ---------------------------------------------------------------------


instance HsValBinds (GHC.Match GHC.Name) where
  hsValBinds (GHC.Match _ _ grhs) = hsValBinds grhs

  replaceValBinds (GHC.Match p t (GHC.GRHSs rhs _binds)) newBinds
    = (GHC.Match p t (GHC.GRHSs rhs binds'))
      where
        binds' = (GHC.HsValBinds newBinds)

  hsTyDecls _ = []

instance HsValBinds (GHC.HsBind GHC.Name) where
  hsValBinds (GHC.PatBind _p rhs _typ _fvs _) = hsValBinds rhs

  -- TODO: ++AZ++ added for compatibility with hsDecls.
  hsValBinds (GHC.FunBind _ _ matches _ _ _) = hsValBinds matches
  hsValBinds other = error $ "hsValBinds (GHC.HsBind GHC.Name) undefined for:" ++ (showGhc other)

  replaceValBinds (GHC.PatBind p (GHC.GRHSs rhs _binds) typ fvs pt) newBinds
    = (GHC.PatBind p (GHC.GRHSs rhs binds') typ fvs pt)
      where
        binds' = (GHC.HsValBinds newBinds)
  replaceValBinds x _newBinds
      = error $ "replaceValBinds (GHC.HsBind GHC.Name) undefined for:" ++ (showGhc x)

  hsTyDecls _ = []

instance HsValBinds (GHC.HsExpr GHC.Name) where
  hsValBinds (GHC.HsLet ds _) = hsValBinds ds
  hsValBinds x = error $ "TypeUtils.hsValBinds undefined for:" ++ showGhc x

  replaceValBinds (GHC.HsLet binds ex) new = (GHC.HsLet (replaceValBinds binds new) ex)
  replaceValBinds old _new = error $ "undefined replaceValBinds (GHC.HsExpr GHC.Name) for:" ++ (showGhc old)

  hsTyDecls _ = []

instance HsValBinds (GHC.Stmt GHC.Name) where
  hsValBinds (GHC.LetStmt ds) = hsValBinds ds
  hsValBinds other = error $ "hsValBinds (GHC.Stmt GHC.Name) undefined for:" ++ (showGhc other)
  replaceValBinds (GHC.LetStmt ds) new = (GHC.LetStmt (replaceValBinds ds new))
  replaceValBinds old _new = error $ "replaceValBinds (GHC.Stmt GHC.Name) undefined for:" ++ (showGhc old)

  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds (GHC.LHsBinds GHC.Name) where
  hsValBinds binds = hsValBinds $ GHC.bagToList binds
  replaceValBinds old _new = error $ "replaceValBinds (GHC.LHsBinds GHC.Name) undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds (GHC.LHsBind GHC.Name) where
  hsValBinds (GHC.L _ (GHC.FunBind _ _ matches _ _ _)) = hsValBinds matches
  hsValBinds (GHC.L _ (GHC.PatBind _ rhs _ _ _))       = hsValBinds rhs
  hsValBinds (GHC.L _ (GHC.VarBind _ rhs _))           = hsValBinds rhs
  hsValBinds (GHC.L _ (GHC.AbsBinds _ _ _ _ binds))    = hsValBinds binds


  replaceValBinds (GHC.L l (GHC.FunBind a b matches c d e)) newBinds
               = (GHC.L l (GHC.FunBind a b (replaceValBinds matches newBinds) c d e))
  replaceValBinds (GHC.L l (GHC.PatBind a rhs b c d)) newBinds
               = (GHC.L l (GHC.PatBind a (replaceValBinds rhs newBinds) b c d))
  replaceValBinds (GHC.L l (GHC.VarBind a rhs b)) newBinds
               = (GHC.L l (GHC.VarBind a (replaceValBinds rhs newBinds) b))
  replaceValBinds (GHC.L l (GHC.AbsBinds a b c d binds)) newBinds
               = (GHC.L l (GHC.AbsBinds a b c d (replaceValBinds binds newBinds)))

  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds ([GHC.LHsBind GHC.Name]) where
  -- hsValBinds xs = concatMap hsValBinds xs -- As in original
  hsValBinds xs = GHC.ValBindsIn (GHC.listToBag xs) []

  replaceValBinds _old (GHC.ValBindsIn b _sigs) = GHC.bagToList b
  replaceValBinds _old (GHC.ValBindsOut rbinds _sigs) = GHC.bagToList $ GHC.unionManyBags $ map (\(_,b) -> b) rbinds

  -- replaceValBinds old new = error ("replaceValBinds (old,new)=" ++ (showGhc (old,new)))

  hsTyDecls _ = []

instance HsValBinds (GHC.LHsExpr GHC.Name) where
  hsValBinds (GHC.L _ (GHC.HsLet binds _ex)) = hsValBinds binds
  hsValBinds _                               = emptyValBinds

  replaceValBinds (GHC.L l (GHC.HsLet binds ex)) newBinds
     = (GHC.L l (GHC.HsLet (replaceValBinds binds newBinds) ex))
  replaceValBinds old _new = error $ "replaceValBinds (GHC.LHsExpr GHC.Name) undefined for:" ++ (showGhc old)

  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds [GHC.LGRHS GHC.Name] where
  hsValBinds xs = unionBinds $ map hsValBinds xs
  replaceValBinds _old _new = error $ "replaceValBinds [GHC.LGRHS GHC.Name] undefined for:" -- ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds (GHC.LGRHS GHC.Name) where
  hsValBinds (GHC.L _ (GHC.GRHS stmts _expr)) = hsValBinds stmts
  replaceValBinds _old _new = error $ "replaceValBinds (GHC.LHGRHS GHC.Name) undefined for:" -- ++ (showGhc _old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds [GHC.LStmt GHC.Name] where
  hsValBinds xs = unionBinds $ map hsValBinds xs
  replaceValBinds old _new = error $ "replaceValBinds [GHC.LStmt GHC.Name] undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds (GHC.LStmt GHC.Name) where
  hsValBinds (GHC.L _ (GHC.LetStmt binds)) = hsValBinds binds
  hsValBinds _                             = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds (GHC.LStmt GHC.Name) undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds [GHC.LPat GHC.Name] where
  hsValBinds _ = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds (GHC.LPat GHC.Name) undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds (GHC.LPat GHC.Name) where
  hsValBinds _ = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds (GHC.LPat GHC.Name) undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds (GHC.Name) where
  hsValBinds _ = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds (GHC.Name) undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds [GHC.SyntaxExpr GHC.Name] where
  hsValBinds _ = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds (GHC.SyntaxExpr GHC.Name) undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds [[GHC.LTyClDecl GHC.Name]] where
  hsValBinds _ = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds [[GHC.LTyClDecl GHC.Name]] undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds [GHC.LTyClDecl GHC.Name] where
  hsValBinds _ = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds [GHC.LTyClDecl GHC.Name] undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds (GHC.LTyClDecl GHC.Name) where
  hsValBinds _ = error $ "hsValBinds (GHC.LTyClDecl GHC.Name) must pull out tcdMeths"
  replaceValBinds old _new = error $ "replaceValBinds (GHC.LTyClDecl GHC.Name) undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds [GHC.LInstDecl GHC.Name] where
  hsValBinds _ = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds [GHC.LInstDecl GHC.Name] undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds (GHC.LInstDecl GHC.Name) where
  hsValBinds _ = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds (GHC.LInstDecl GHC.Name) undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds (GHC.LHsType GHC.Name) where
  hsValBinds _ = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds (GHC.LHsType GHC.Name) undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds [GHC.LSig GHC.Name] where
  hsValBinds _ = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds [GHC.LSig GHC.Name] undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds (GHC.LSig GHC.Name) where
  hsValBinds _ = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds (GHC.LSig GHC.Name) undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

#if __GLASGOW_HASKELL__ > 704
instance HsValBinds [GHC.LFamInstDecl GHC.Name] where
  hsValBinds _ = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds [GHC.LFamInstDecl GHC.Name] undefined for:" ++ (showGhc old)
  hsTyDecls _ = []
#endif

-- ---------------------------------------------------------------------

#if __GLASGOW_HASKELL__ > 704
instance HsValBinds (GHC.LFamInstDecl GHC.Name) where
  hsValBinds _ = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds (GHC.LFamInstDecl GHC.Name) undefined for:" ++ (showGhc old)
  hsTyDecls _ = []
#endif

-- ---------------------------------------------------------------------

instance HsValBinds (GHC.HsIPBinds GHC.Name) where
  hsValBinds _ = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds (GHC.HsIPBinds GHC.Name) undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------
-}

-- ---------------------------------------------------------------------

class (SYB.Data a, SYB.Typeable a) => FindEntity a where

  -- | Returns True is a syntax phrase, say a, is part of another
  -- syntax phrase, say b.
  -- NOTE: very important: only do a shallow check
  findEntity:: (SYB.Data b, SYB.Typeable b) => a -> b -> Bool

-- ---------------------------------------------------------------------

instance FindEntity GHC.Name where

  findEntity n t = fromMaybe False res
   where
    res = somethingStaged SYB.Renamer Nothing (Nothing `SYB.mkQ` worker) t

    worker (name::GHC.Name)
      | n == name = Just True
    worker _ = Nothing

-- ---------------------------------------------------------------------

-- TODO: should the location be matched too in this case?
instance FindEntity (GHC.Located GHC.Name) where

  findEntity n t = fromMaybe False res
   where
    res = somethingStaged SYB.Renamer Nothing (Nothing `SYB.mkQ` worker) t

    worker (name::GHC.Located GHC.Name)
      | n == name = Just True
    worker _ = Nothing


-- ---------------------------------------------------------------------

instance FindEntity (GHC.Located (GHC.HsExpr GHC.Name)) where

  findEntity e t = fromMaybe False res
   where
    res = somethingStaged SYB.Renamer Nothing (Nothing `SYB.mkQ` worker) t

    worker (expr::GHC.Located (GHC.HsExpr GHC.Name))
      | sameOccurrence e expr = Just True
    worker _ = Nothing

-- ---------------------------------------------------------------------

instance FindEntity (GHC.Located (GHC.HsBindLR GHC.Name GHC.Name)) where
  findEntity e t = fromMaybe False res
   where
    res = somethingStaged SYB.Renamer Nothing (Nothing `SYB.mkQ` worker) t

    worker (expr::(GHC.Located (GHC.HsBindLR GHC.Name GHC.Name)))
      | sameOccurrence e expr = Just True
    worker _ = Nothing

instance FindEntity (GHC.Located (GHC.HsDecl GHC.Name)) where
  findEntity d t = fromMaybe False res
   where
    res = somethingStaged SYB.Renamer Nothing (Nothing `SYB.mkQ` worker) t

    worker (decl::(GHC.Located (GHC.HsDecl GHC.Name)))
      | sameOccurrence d decl = Just True
    worker _ = Nothing

-- ---------------------------------------------------------------------


-- | Returns True is a syntax phrase, say a, is part of another syntax
-- phrase, say b.
-- Expects to be at least Parser output
findEntity':: (SYB.Data a, SYB.Data b)
              => a -> b -> Maybe (SimpPos,SimpPos)
findEntity' a b = res
  where
    -- ++AZ++ do a generic traversal, and see if it matches.
    res = somethingStaged SYB.Parser Nothing worker b

    worker :: (SYB.Typeable c,SYB.Data c)
           => c -> Maybe (SimpPos,SimpPos)
    worker x = if SYB.typeOf a == SYB.typeOf x
                 -- then Just (getStartEndLoc b == getStartEndLoc a)
                 then Just (getStartEndLoc x)
                 else Nothing

-- ---------------------------------------------------------------------

-- |Find those declarations(function\/pattern binding) which define
-- the specified GHC.Names. incTypeSig indicates whether the
-- corresponding type signature will be included.
definingDeclsNames::
            [GHC.Name]   -- ^ The specified identifiers.
            ->[GHC.LHsBind GHC.Name] -- ^ A collection of declarations.
            ->Bool       -- ^ True means to include the type signature.
            ->Bool       -- ^ True means to look at the local declarations as well. 
            ->[GHC.LHsBind GHC.Name]  -- ^ The result.
definingDeclsNames pns ds _incTypeSig recursive = concatMap defining ds
  where
   defining decl
     = if recursive
        then SYB.everythingStaged SYB.Renamer (++) [] ([]  `SYB.mkQ` defines') decl
        else defines' decl
     where
      defines' :: (GHC.LHsBind GHC.Name) -> [GHC.LHsBind GHC.Name]
      defines' decl'@(GHC.L _ (GHC.FunBind (GHC.L _ pname) _ _ _ _ _))
        |isJust (find (==(pname)) pns) = [decl']

      defines' decl'@(GHC.L _l (GHC.PatBind p _rhs _ty _fvs _))
        |(hsNamess p) `intersect` pns /= [] = [decl']

      defines' _ = []

-- |Find those declarations(function\/pattern binding) which define
-- the specified GHC.Names. incTypeSig indicates whether the
-- corresponding type signature will be included.
definingDeclsNames':: (SYB.Data t)
            => [GHC.Name]   -- ^ The specified identifiers.
            -> t -- ^ A collection of declarations.
            ->[GHC.LHsBind GHC.Name]  -- ^ The result.
definingDeclsNames' pns t = defining t
  where
   defining decl
     = SYB.everythingStaged SYB.Renamer (++) [] ([]  `SYB.mkQ` defines') decl
     where
      defines' :: (GHC.LHsBind GHC.Name) -> [GHC.LHsBind GHC.Name]
      defines' decl'@(GHC.L _ (GHC.FunBind (GHC.L _ pname) _ _ _ _ _))
        |isJust (find (==(pname)) pns) = [decl']

      defines' decl'@(GHC.L _l (GHC.PatBind p _rhs _ty _fvs _))
        |(hsNamess p) `intersect` pns /= [] = [decl']

      defines' _ = []

-- ---------------------------------------------------------------------

-- |Find those type signatures for the specified GHC.Names.
definingSigsNames :: (SYB.Data t) =>
            [GHC.Name] -- ^ The specified identifiers.
            ->t        -- ^ A collection of declarations.
            ->[GHC.LSig GHC.Name]  -- ^ The result.
definingSigsNames pns ds = def ds
  where
   def decl
     = SYB.everythingStaged SYB.Renamer (++) [] ([]  `SYB.mkQ` inSig) decl
     where
      inSig :: (GHC.LSig GHC.Name) -> [GHC.LSig GHC.Name]
      inSig (GHC.L l (GHC.TypeSig ns t))
       | defines' ns /= [] = [(GHC.L l (GHC.TypeSig (defines' ns) t))]
      inSig _ = []

      defines' (p::[GHC.Located GHC.Name])
        = filter (\(GHC.L _ n) -> n `elem` pns) p

-- ---------------------------------------------------------------------

-- |Find those declarations which define the specified GHC.Names.
definingTyClDeclsNames:: (SYB.Data t)
            => [GHC.Name]   -- ^ The specified identifiers.
            -> t -- ^ A collection of declarations.
            ->[GHC.LTyClDecl GHC.Name]  -- ^ The result.
definingTyClDeclsNames pns t = defining t
  where
   defining decl
     = SYB.everythingStaged SYB.Renamer (++) [] ([]  `SYB.mkQ` defines') decl
     where
      defines' :: (GHC.LTyClDecl GHC.Name) -> [GHC.LTyClDecl GHC.Name]
      defines' decl'@(GHC.L _ (GHC.ForeignType (GHC.L _ pname) _ ))
        |isJust (find (==(pname)) pns) = [decl']

      -- NOTE: GHC 7.4.2 returns family instances as TyData, GHC 7.6.3
      -- returns them as a separate FamInstDecl

      defines' decl'@(GHC.L _ (GHC.TyFamily _ (GHC.L _ pname) _ _))
        |isJust (find (==(pname)) pns) = [decl']

#if __GLASGOW_HASKELL__ > 704
      defines' decl'@(GHC.L _ (GHC.TyDecl (GHC.L _ pname) _ _ _))
#else
      defines' decl'@(GHC.L _ (GHC.TyData _ _ (GHC.L _ pname) _ _ _ __ _))
#endif
        |isJust (find (==(pname)) pns) = [decl']

#if __GLASGOW_HASKELL__ > 704
#else
      defines' decl'@(GHC.L _ (GHC.TySynonym (GHC.L _ pname) _ _ _))
        |isJust (find (==(pname)) pns) = [decl']
#endif

#if __GLASGOW_HASKELL__ > 704
      defines' decl'@(GHC.L _ (GHC.ClassDecl _ (GHC.L _ pname) _ _ _ _ _ _ _ _))
#else
      defines' decl'@(GHC.L _ (GHC.ClassDecl _ (GHC.L _ pname) _ _ _ _ _ _ _))
#endif
        |isJust (find (==(pname)) pns) = [decl']

      defines' _ = []

-- ---------------------------------------------------------------------

-- TODO: AZ: pretty sure this can be simplified, depends if we need to
--          manage transformed stuff too though.

-- | Return True if syntax phrases t1 and t2 refer to the same one.
sameOccurrence :: (GHC.Located t) -> (GHC.Located t) -> Bool
sameOccurrence (GHC.L l1 _) (GHC.L l2 _)
 = l1 == l2


-- ---------------------------------------------------------------------

-- | Return True if the function\/pattern binding defines the
-- specified identifier.
defines:: GHC.Name -> GHC.LHsBind GHC.Name -> Bool
defines n (GHC.L _ (GHC.FunBind (GHC.L _ pname) _ _ _ _ _))
 = pname == n
defines n (GHC.L _ (GHC.PatBind p _rhs _ty _fvs _))
 = elem n (hsNamess p)
defines _ _= False

definesP::PName->HsDeclP->Bool
definesP pn (GHC.L _ (GHC.ValD (GHC.FunBind (GHC.L _ pname) _ _ _ _ _)))
 = PN pname == pn
definesP pn (GHC.L _ (GHC.ValD (GHC.PatBind p _rhs _ty _fvs _)))
 = elem pn (hsPNs p)
definesP _ _= False


-- | Return True if the declaration defines the type signature of the
-- specified identifier.
definesTypeSig :: GHC.Name -> GHC.LSig GHC.Name -> Bool
definesTypeSig pn (GHC.L _ (GHC.TypeSig names _typ)) = elem pn $ map (\(GHC.L _ n)->n) names
definesTypeSig _  _ =False


{-
-- | Return True if the declaration defines the type signature of the specified identifier.
isTypeSigOf :: PNT -> HsDeclP -> Bool
isTypeSigOf pnt (TiDecorate.Dec (HsTypeSig loc is c tp))= elem pnt is
isTypeSigOf _  _ =False
-}


-- | Return the list of identifiers (in PName format) defined by a function\/pattern binding.
definedPNs::GHC.LHsBind GHC.Name -> [GHC.Name]
definedPNs (GHC.L _ (GHC.FunBind (GHC.L _ pname) _ _ _ _ _)) = [pname]
definedPNs (GHC.L _ (GHC.PatBind p _rhs _ty _fvs _))         = (hsNamess p)
definedPNs (GHC.L _ (GHC.VarBind pname _rhs _))              = [pname]

-- TODO: what about GHC.AbsBinds?
definedPNs  _ = []


--------------------------------------------------------------------------------

sameBind :: GHC.LHsBind GHC.Name -> GHC.LHsBind GHC.Name -> Bool
sameBind b1 b2 = (definedPNs b1) == (definedPNs b2)

-- ---------------------------------------------------------------------

-- TODO: is this the same is isUsedInRhs?
class (SYB.Data t) => UsedByRhs t where

    -- | Return True if any of the GHC.Name's appear in the given
    -- syntax element
    usedByRhs:: t -> [GHC.Name] -> Bool

instance UsedByRhs GHC.RenamedSource where

   -- Defined like this in the original
   usedByRhs _renamed _pns = False
   -- usedByRhs renamed pns = usedByRhs (hsValBinds renamed) pns -- ++AZ++

instance UsedByRhs (GHC.LHsBinds GHC.Name) where
  usedByRhs binds pns = or $ map (\b -> usedByRhs b pns) $ GHC.bagToList binds

instance UsedByRhs (GHC.HsValBinds GHC.Name) where
  usedByRhs (GHC.ValBindsIn binds _sigs) pns  = usedByRhs (GHC.bagToList binds) pns
  usedByRhs (GHC.ValBindsOut binds _sigs) pns = or $ map (\(_,b) -> usedByRhs b pns) binds

instance UsedByRhs (GHC.Match GHC.Name) where
  usedByRhs (GHC.Match _ _ (GHC.GRHSs rhs _)) pns -- = usedByRhs (hsValBinds rhs) pns
                                                  = findPNs pns rhs

instance UsedByRhs [GHC.LHsBind GHC.Name] where
  usedByRhs binds pns = or $ map (\b -> usedByRhs b pns) binds

instance UsedByRhs (GHC.HsBind GHC.Name) where
  usedByRhs (GHC.FunBind _ _ matches _ _ _) pns = findPNs pns matches
  usedByRhs (GHC.PatBind _ rhs _ _ _)       pns = findPNs pns rhs
  usedByRhs (GHC.VarBind _ rhs _)           pns = findPNs pns rhs
  usedByRhs (GHC.AbsBinds _ _ _ _ _)       _pns = False

instance UsedByRhs (GHC.LHsBind GHC.Name) where
  usedByRhs (GHC.L _ bind) pns = usedByRhs bind pns

instance UsedByRhs (GHC.LHsExpr GHC.Name) where
  usedByRhs (GHC.L _ e) pns = usedByRhs e pns

instance UsedByRhs (GHC.HsExpr GHC.Name) where
  usedByRhs (GHC.HsLet _lb e) pns = findPNs pns e
  usedByRhs e                _pns = error $ "undefined usedByRhs:" ++ (showGhc e)

instance UsedByRhs (GHC.Stmt GHC.Name) where
  usedByRhs (GHC.LetStmt lb) pns = findPNs pns lb
  usedByRhs s               _pns = error $ "undefined usedByRhs:" ++ (showGhc s)


--------------------------------------------------------------------------------

-- |Find the identifier(in GHC.Name format) whose start position is
-- (row,col) in the file specified by the fileName, and returns
-- `Nothing` if such an identifier does not exist.
locToName::(SYB.Data t)
                    =>SimpPos          -- ^ The row and column number
                    ->t                -- ^ The syntax phrase
                    -> Maybe (GHC.Located GHC.Name)  -- ^ The result
locToName (row,col) t = locToName' SYB.Renamer (row,col) t

-- |Find the identifier(in GHC.RdrName format) whose start position is
-- (row,col) in the file specified by the fileName, and returns
-- `Nothing` if such an identifier does not exist.
locToRdrName::(SYB.Data t)
                    =>SimpPos          -- ^ The row and column number
                    ->t                -- ^ The syntax phrase
                    -> Maybe (GHC.Located GHC.RdrName)  -- ^ The result
locToRdrName (row,col) t = locToName' SYB.Parser (row,col) t


-- |Worker for both locToName and locToRdrName.
-- NOTE: provides for FunBind MatchGroups where only the first name is
-- retained in the AST
locToName'::(SYB.Data t, SYB.Data a, Eq a,GHC.Outputable a)
                    =>SYB.Stage
                    ->SimpPos          -- ^ The row and column number
                    ->t                -- ^ The syntax phrase
                    -> Maybe (GHC.Located a)  -- ^ The result
locToName' stage (row,col) t =
      if res1 /= Nothing
        then res1
        else res2
     where
        res1 = somethingStaged stage Nothing
            (Nothing `SYB.mkQ` worker
                     `SYB.extQ` workerBind
                     `SYB.extQ` workerExpr
                     `SYB.extQ` workerLIE
                     `SYB.extQ` workerHsTyVarBndr
                     `SYB.extQ` workerLHsType
                     ) t

        res2 = somethingStaged stage Nothing
            (Nothing `SYB.mkQ` workerFunBind) t

        {-
        res = reverse $ everythingStaged SYB.Renamer (++) []
            ([] `SYB.mkQ` workerFunBind `SYB.extQ` worker `SYB.extQ` workerBind `SYB.extQ` workerExpr) t

        res' = case res of
          [] -> Nothing
          xs -> Just (head xs)
        -}
        -- A FunBind has a MatchGroup, which lists all the possible
        -- bindings. Hence
        --   x 0 = 0
        --   x y = 2 * y
        -- Will have a single FunBind, with name x and using the
        -- specific (GHC.L l GHC.Name) of the x on the first line.
        -- Attempting to find the variable x on the second line will
        -- fail, it needs to be deduced from a FunBind having more
        -- than one match. The Located Match includes the original
        -- variable name in the location, but not in the match contents
        workerFunBind ((GHC.FunBind pnt _ (GHC.MatchGroup matches _) _ _ _) :: (GHC.HsBindLR a a))
          | nonEmptyList match = Just pnt
          where
            -- match = error $ "locToName':matches=" ++ (showGhc $ map (\(GHC.L l _) -> l) matches)
            match = filter inScope (tail matches)
            -- match = filter inScope (matches)
        workerFunBind _ = Nothing

        worker (pnt :: (GHC.Located a))
          | inScope pnt = Just pnt
        worker _ = Nothing

        workerBind pnt@(GHC.L l (GHC.VarPat name) :: (GHC.Located (GHC.Pat a)))
          | inScope pnt = Just (GHC.L l name)
        workerBind _ = Nothing

        workerExpr (pnt@(GHC.L l (GHC.HsVar name)) :: (GHC.Located (GHC.HsExpr a)))
          | inScope pnt = Just (GHC.L l name)
        workerExpr _ = Nothing

        workerLIE (pnt@(GHC.L l (GHC.IEVar name)) :: (GHC.LIE a))
          | inScope pnt = Just (GHC.L l name)
        workerLIE _ = Nothing

#if __GLASGOW_HASKELL__ > 704
        workerHsTyVarBndr (pnt@(GHC.L l (GHC.UserTyVar name))::  (GHC.LHsTyVarBndr a))
#else
        workerHsTyVarBndr (pnt@(GHC.L l (GHC.UserTyVar name _typ))::  (GHC.LHsTyVarBndr a))
#endif
          | inScope pnt = Just (GHC.L l name)
        workerHsTyVarBndr _ = Nothing

        workerLHsType (pnt@(GHC.L l (GHC.HsTyVar name)):: (GHC.LHsType a))
          | inScope pnt = Just (GHC.L l name)
        workerLHsType _ = Nothing


        inScope :: GHC.Located e -> Bool
        inScope (GHC.L l _) =
          case l of
            (GHC.UnhelpfulSpan _) -> False
            (GHC.RealSrcSpan ss)  ->
              -- (GHC.srcSpanFile ss == fileName) &&
              (GHC.srcSpanStartLine ss <= row) &&
              (GHC.srcSpanEndLine ss   >= row) &&
              (col >= (GHC.srcSpanStartCol ss)) &&
              (col <= (GHC.srcSpanEndCol   ss))


--------------------------------------------------------------------------------

-- |Find all Located Names in the given Syntax phrase.
allNames::(SYB.Data t)
       =>t                      -- ^ The syntax phrase
       ->[GHC.Located GHC.Name] -- ^ The result
allNames t
  = res
       where
        res = SYB.everythingStaged SYB.Parser (++) []
            ([] `SYB.mkQ` worker `SYB.extQ` workerBind `SYB.extQ` workerExpr) t

        worker (pnt :: (GHC.Located GHC.Name))
          = [pnt]
        -- worker _ = []

        workerBind (GHC.L l (GHC.VarPat name) :: (GHC.Located (GHC.Pat GHC.Name)))
          = [(GHC.L l name)]
        workerBind _ = []

        workerExpr ((GHC.L l (GHC.HsVar name)) :: (GHC.Located (GHC.HsExpr GHC.Name)))
          = [(GHC.L l name)]
        workerExpr _ = []



--------------------------------------------------------------------------------

-- |Find the identifier with the given name. This looks through the
-- given syntax phrase for the first GHC.Name which matches. Because
-- it is Renamed source, the GHC.Name will include its defining
-- location. Returns Nothing if the name is not found.

getName::(SYB.Data t)=> String           -- ^ The name to find
                     -> t                -- ^ The syntax phrase
                     -> Maybe GHC.Name   -- ^ The result
getName str t
  = res
       where
        res = somethingStaged SYB.Renamer Nothing
            (Nothing `SYB.mkQ` worker `SYB.extQ` workerBind `SYB.extQ` workerExpr) t

        worker ((GHC.L _ n) :: (GHC.Located GHC.Name))
          | showGhc n == str = Just n
        worker _ = Nothing

        workerBind (GHC.L _ (GHC.VarPat name) :: (GHC.Located (GHC.Pat GHC.Name)))
          | showGhc name == str = Just name
        workerBind _ = Nothing


        workerExpr ((GHC.L _ (GHC.HsVar name)) :: (GHC.Located (GHC.HsExpr GHC.Name)))
          | showGhc name == str = Just name
        workerExpr _ = Nothing

-- ---------------------------------------------------------------------

-- | Add identifiers to the export list of a module. If the second argument is like: Just p, then do the adding only if p occurs
-- in the export list, and the new identifiers are added right after p in the export list. Otherwise the new identifiers are add
-- to the beginning of the export list. In the case that the export list is emport, then if the third argument is True, then create
-- an explict export list to contain only the new identifiers, otherwise do nothing.

addImportDecl ::
    GHC.RenamedSource
    -> GHC.ModuleName
    -> Maybe GHC.FastString -- ^qualifier
    -> Bool -> Bool -> Bool
    -> Maybe String         -- ^alias
    -> Bool
    -> [GHC.Name]
    -> RefactGhc GHC.RenamedSource
addImportDecl (groupedDecls,imp, b, c) modName pkgQual source safe qualify alias hide idNames
  = do
       toks <- fetchToks
       let toks1
               =if length imps' > 0
                   then let (_startLoc, endLoc) = getStartEndLoc $ last imps'
                            toks1' = getToks ((1,1),endLoc) toks
                        in toks1'
                   else if not $ isEmptyGroup groupedDecls
                          then
                               let startLoc = fst $ startEndLocIncComments toks groupedDecls
                                   (toks1', _toks2') = break (\t ->tokenPos t==startLoc) toks
                               in toks1'
                          else toks

       -- drawTokenTreeDetailed "before starting"
       logm $ "addImportDecl:toks =" ++ show toks
       logm $ "addImportDecl:toks1=" ++ show toks1

       let lastTok = ghead "addImportDecl" $ dropWhile isWhiteSpace $ reverse toks1
       let startPos = tokenPos    lastTok
       let endPos   = tokenPosEnd lastTok

       let newToks = basicTokenise (showGhc impDecl)
       logm $ "addImportDecl:newToks=" ++ (show newToks) -- ++AZ++
       void $ addToksAfterPos (startPos,endPos) (PlaceOffset 1 0 1) newToks
       return (groupedDecls, (imp++[(mkNewLSomething impDecl)]), b, c)
  where

     alias' = case alias of
                  Just stringName -> Just $ GHC.mkModuleName stringName
                  _               -> Nothing

     impDecl = GHC.ImportDecl {
                        GHC.ideclName        = mkNewLModuleName modName
                        , GHC.ideclPkgQual   = pkgQual
                        , GHC.ideclSource    = source
                        , GHC.ideclSafe      = safe
                        , GHC.ideclQualified = qualify
                        , GHC.ideclImplicit  = False
                        , GHC.ideclAs        = alias'
                        , GHC.ideclHiding    =
                                      (if idNames == [] && hide == False then
                                            Nothing
                                       else
                                            (Just (hide, map mkNewEnt idNames)))
                }
     imps' = rmPreludeImports imp

     mkNewLSomething :: a -> GHC.Located a
     mkNewLSomething a = (GHC.L l a) where
        filename = (GHC.mkFastString "f")
        l = GHC.mkSrcSpan (GHC.mkSrcLoc filename 1 1) (GHC.mkSrcLoc filename 1 1)


     mkNewLModuleName :: GHC.ModuleName -> GHC.Located GHC.ModuleName
     mkNewLModuleName moduName = mkNewLSomething moduName

-- ---------------------------------------------------------------------

isEmptyGroup :: GHC.HsGroup id -> Bool
isEmptyGroup x = (==0) $ sum $
   [valds, tyclds, instds, derivds, fixds, defds, fords, warnds, annds, ruleds, vects, docs]
  where
    valds = size $ GHC.hs_valds x

    size :: GHC.HsValBindsLR idL idR -> Int
    size (GHC.ValBindsIn lhsBinds sigs) = (length sigs) + (length . GHC.bagToList $ lhsBinds)
    size (GHC.ValBindsOut recFlags lsigs) = (length lsigs) + (length recFlags)

    tyclds = length $ GHC.hs_tyclds x

    instds = length $ GHC.hs_instds x

    derivds = length $ GHC.hs_derivds x

    fixds = length $ GHC.hs_fixds x

    defds = length $ GHC.hs_defds x

    fords = length $ GHC.hs_fords x

    warnds = length $ GHC.hs_warnds x

    annds = length $ GHC.hs_annds x

    ruleds = length $ GHC.hs_ruleds x

    vects = length $ GHC.hs_vects x

    docs = length $ GHC.hs_docs x


-- | Remove ImportDecl from the imports list, commonly returned from a RenamedSource type, so it can
-- be further processed.
--rmPreludeImports :: [GHC.Located (GHC.ImportDecl GHC.Name)] -> [GHC.Located (GHC.ImportDecl GHC.Name)]
rmPreludeImports ::
  [GHC.Located (GHC.ImportDecl GHC.Name)]
  -> [GHC.Located (GHC.ImportDecl GHC.Name)]
rmPreludeImports = filter isPrelude where
            isPrelude = (/="Prelude") . GHC.moduleNameString . GHC.unLoc . GHC.ideclName . GHC.unLoc


-- ---------------------------------------------------------------------

-- |Make a new set of tokens, originating at (0,0), for a given
-- declaration and optional signature.
-- NOTE: This function returns tokens originating at (0,0), to be
-- stitched in at the right place by TokenUtils
makeNewToks :: (GHC.LHsBind GHC.Name, [GHC.LSig GHC.Name], Maybe [PosToken])
              -> RefactGhc [PosToken]
makeNewToks (decl, maybeSig, declToks) = do
   let
     declStr = case declToks of
                Just ts -> "\n" ++ (unlines $ dropWhile (\l -> l == "") $ lines $ GHC.showRichTokenStream $ reAlignMarked ts)
                Nothing -> "\n"++(prettyprint decl)++"\n\n"
     sigStr  = case declToks of
                Just _ts -> ""
                Nothing -> "\n" ++ (intercalate "\n" $ map prettyprint maybeSig)
   -- logm $ "makeNewToks:declStr=[" ++ declStr ++ "]"
   let newToks = tokenise ((0,0),(0,0)) 0 True (sigStr ++ declStr)
   return newToks

-- ---------------------------------------------------------------------

-- | Adding a declaration to the declaration list of the given syntax
-- phrase. If the second argument is Nothing, then the declaration
-- will be added to the beginning of the declaration list, but after
-- the data type declarations is there is any.
addDecl:: (SYB.Data t,HsValBinds t)
        => t              -- ^The AST to be updated
        -> Maybe GHC.Name -- ^If this is Just, then the declaration
                          -- will be added right after this
                          -- identifier's definition.
        -> (GHC.LHsBind GHC.Name, [GHC.LSig GHC.Name], Maybe [PosToken])
             -- ^ The declaration with optional signatures to be added,
             -- in both AST and Token stream format (optional). If
             -- signature and tokens provided, the tokens should
             -- include the signature too
        -> Bool              -- ^ True means the declaration is a
                             -- toplevel declaration.
        -> RefactGhc t

addDecl parent pn (decl, msig, declToks) topLevel
 = if isJust pn
     then appendDecl parent (gfromJust "addDecl" pn) (decl, msig, declToks)
     else if topLevel
            then addTopLevelDecl (decl, msig, declToks) parent
            else addLocalDecl parent (decl,msig,declToks)
 where

  -- ^Add a definition to the beginning of the definition declaration
  -- list, but after the data type declarations if there is any. The
  -- definition will be pretty-printed if its token stream is not
  -- provided.
  addTopLevelDecl :: (SYB.Data t, HsValBinds t)
       => (GHC.LHsBind GHC.Name, [GHC.LSig GHC.Name], Maybe [PosToken])
       -> t -> RefactGhc t
  addTopLevelDecl (newDecl, maybeSig, maybeDeclToks) parent'
    = do let binds = hsValBinds parent'
             decls = hsBinds parent'
             (decls1,decls2) = break (\x->isFunOrPatBindR x {- was || isTypeSig x -}) decls

         newToks <- makeNewToks (newDecl,maybeSig,maybeDeclToks)
         logm $ "addTopLevelDecl:newToks=" ++ (show newToks)

         let Just sspan = if (emptyList decls2)
                            then getSrcSpan (glast "addTopLevelDecl" decls1)
                            else getSrcSpan (ghead "addTopLevelDecl" decls2)

         decl' <- putDeclToksAfterSpan sspan newDecl (PlaceOffset 2 0 2) newToks

         return (replaceValBinds parent' (GHC.ValBindsIn (GHC.listToBag (decls1++[decl']++decls2)) (maybeSig++(getValBindSigs binds))))

  appendDecl :: (SYB.Data t, HsValBinds t)
      => t        -- ^Original AST
      -> GHC.Name -- ^Name to add the declaration after
      -> (GHC.LHsBind GHC.Name, [GHC.LSig GHC.Name], Maybe [PosToken]) -- ^declaration and maybe sig/tokens
      -> RefactGhc t -- ^updated AST
  appendDecl parent' pn' (newDecl, maybeSig, declToks')
    = do let binds = hsValBinds parent'
         -- logm $ "appendDecl:declToks=" ++ (show declToks')
         newToks <- makeNewToks (newDecl,maybeSig,declToks')
         -- logm $ "appendDecl:newToks=" ++ (show newToks)

         let Just sspan = getSrcSpan $ ghead "appendDecl" after
         decl' <- putDeclToksAfterSpan sspan newDecl (PlaceOffset 2 0 2) newToks

         let decls1 = before ++ [ghead "appendDecl14" after]
             decls2 = gtail "appendDecl15" after
         {-
         case maybeSig of
           Nothing  -> return (replaceBinds    parent (decls1++[decl']++decls2))
           Just sig -> return (replaceValBinds parent (GHC.ValBindsIn (GHC.listToBag (decls1++[decl']++decls2)) (sig:(getValBindSigs binds))))
         -}
         return (replaceValBinds parent' (GHC.ValBindsIn (GHC.listToBag (decls1++[decl']++decls2)) (maybeSig++(getValBindSigs binds))))
      where
        decls = hsBinds parent'
        (before,after) = break (defines pn') decls -- Need to handle the case that 'after' is empty?


  addLocalDecl :: (SYB.Data t, HsValBinds t)
               => t -> (GHC.LHsBind GHC.Name, [GHC.LSig GHC.Name], Maybe [PosToken])
               -> RefactGhc t
  addLocalDecl parent' (newFun, maybeSig, newFunToks)
    =do
        let binds = hsValBinds parent'

        let (startLoc@((_,prevCol)),endLoc)
             = if (emptyList localDecls)
                 then getStartEndLoc parent'
                 else getStartEndLoc localDecls

        let newToks = basicTokenise newSource

        (newFun',_) <- addLocInfo (newFun, newToks)

        let rowIndent = 1

        if (emptyList localDecls)
          then
            void $ addToksAfterPos (startLoc,endLoc) (PlaceOffset rowIndent 4 2) newToks
          else
            void $ addToksAfterPos (startLoc,endLoc) (PlaceAbsCol (rowIndent+1) prevCol 2) newToks


        return (replaceValBinds parent' (GHC.ValBindsIn (GHC.listToBag ((hsBinds parent' ++ [newFun']))) (maybeSig++(getValBindSigs binds))))
    where
         localDecls = hsBinds parent'

         -- TODO: where tokens are passed in, first normalise them to
         -- the left column before adding in the where clause part
         newSource = if (emptyList localDecls)
                       then "where\n"++ concatMap (\l-> "   "++l++"\n") (lines newFun')
                       else ("" ++ newFun'++"\n")
           where
            newFun' = unlines $ stripLeadingSpaces $ lines $ sigStr ++ newFunBody
            newFunBody = case newFunToks of
                           Just ts -> unlines $ dropWhile (\l -> l == "") $ lines $ GHC.showRichTokenStream $ reAlignMarked ts
                           Nothing -> prettyprint newFun

            sigStr  = case newFunToks of
                        Just _ts -> ""
                        Nothing -> if (emptyList maybeSig)
                                     then ""
                                     else (intercalate "\n" $ map prettyprint maybeSig) ++ "\n"

-- ---------------------------------------------------------------------

-- |Take a list of strings and return a list with the longest prefix
-- of spaces removed
stripLeadingSpaces :: [String] -> [String]
stripLeadingSpaces xs = map (drop n) xs
  where
    n = minimum $ map oneLen xs

    oneLen x = length prefix
      where
        (prefix,_) = break (/=' ') x

-- ---------------------------------------------------------------------

-- | add items to the hiding list of an import declaration which
-- imports the specified module.
addHiding::
    GHC.ModuleName       -- ^ The imported module name
  ->GHC.RenamedSource    -- ^ The current module
  ->[GHC.Name]           -- ^ The items to be added
  ->RefactGhc GHC.RenamedSource -- ^ The result (with token stream updated)
addHiding a b c = addItemsToImport' a b c Hide

-- | Creates a new entity for hiding a name in an ImportDecl.
mkNewEnt :: GHC.Name -> GHC.LIE GHC.Name
mkNewEnt pn = (GHC.L l (GHC.IEVar pn))
 where
   filename = (GHC.mkFastString "f")
   l = GHC.mkSrcSpan (GHC.mkSrcLoc filename 1 1) (GHC.mkSrcLoc filename 1 1)

-- | Represents the operation type we want to select on addItemsToImport'
data ImportType = Hide     -- ^ Used for addHiding
                | Import   -- ^ Used for addItemsToImport

-- | Add identifiers (given by the third argument) to the explicit entity list in the declaration importing the
--   specified module name. This function does nothing if the import declaration does not have an explicit entity list. 
addItemsToImport::
    GHC.ModuleName       -- ^ The imported module name
  ->GHC.RenamedSource    -- ^ The current module
  ->[GHC.Name]           -- ^ The items to be added
--  ->Maybe GHC.Name       -- ^ The condition identifier.
  ->RefactGhc GHC.RenamedSource -- ^ The result (with token stream updated)
addItemsToImport a b c = addItemsToImport' a b c Import

-- | Add identifiers (given by the third argument) to the explicit entity list in the declaration importing the
--   specified module name. If the ImportType argument is Hide, then the items will be added to the "hiding"
--   list. If it is Import, they will be added to the explicit import entries. This function does nothing if 
--   the import declaration does not have an explicit entity list and ImportType is Import.
addItemsToImport'::
    GHC.ModuleName       -- ^ The imported module name
  ->GHC.RenamedSource    -- ^ The current module
  ->[GHC.Name]           -- ^ The items to be added
--  ->Maybe GHC.Name       -- ^ The condition identifier.
  ->ImportType           -- ^ Whether to hide the names or import them. Uses special data for clarity.
  ->RefactGhc GHC.RenamedSource -- ^ The result (with token stream updated)
addItemsToImport' serverModName (g,imps,e,d) pns impType = do
    imps' <- mapM inImport imps
    return (g,imps',e,d)
  where
    isHide = case impType of
             Hide   -> True
             Import -> False

    inImport :: GHC.LImportDecl GHC.Name -> RefactGhc (GHC.LImportDecl GHC.Name)
    inImport imp@(GHC.L _ (GHC.ImportDecl (GHC.L _ modName) _qualify _source _safe isQualified _isImplicit _as h))
      | serverModName == modName  && not isQualified -- && (if isJust pn then findPN (gfromJust "addItemsToImport" pn) h else True)
       = case h of
           Nothing              -> insertEnts imp [] True
           Just (_isHide, ents) -> insertEnts imp ents False
    inImport x = return x

    insertEnts ::
      GHC.LImportDecl GHC.Name
      -> [GHC.LIE GHC.Name]
      -> Bool
      -> RefactGhc ( GHC.LImportDecl GHC.Name )
    insertEnts imp ents isNew =
        if isNew && not isHide then return imp
        else do
            toks <- fetchToks
            let (startPos,endPos) = getStartEndLoc imp
                ((GHC.L l t),s) = ghead "addHiding" $ reverse $ getToks (startPos,endPos) toks
                start = getGhcLoc l
                end   = getGhcLocEnd l

                beginning =
                        if isNew then
                            s ++ (if isHide then " hiding " else " ")++"("
                        else ","
                ending = if isNew then ")" else s

                newToken=mkToken t start (beginning++showEntities showGhc pns ++ending)
                -- toks'=replaceToks toks start end [newToken]
                -- toks'=replaceTok toks start newToken

            void $ putToksForPos (start,end) [newToken]

            return (replaceHiding imp  (Just (isHide, (map mkNewEnt  pns)++ents)))


    replaceHiding (GHC.L l (GHC.ImportDecl mn q src safe isQ isImp as _h)) h1 =
         (GHC.L l (GHC.ImportDecl mn q src safe isQ isImp as h1))

-- ---------------------------------------------------------------------

addParamsToDecls::
        [GHC.LHsBind GHC.Name] -- ^ A declaration list where the function is defined and\/or used.
      ->GHC.Name    -- ^ The function name.
      ->[GHC.Name]  -- ^ The parameters to be added.
      ->Bool        -- ^ Modify the token stream or not.
      ->RefactGhc [GHC.LHsBind GHC.Name] -- ^ The result.

addParamsToDecls decls pn paramPNames modifyToks = do
  logm $ "addParamsToDecls (pn,paramPNames,modifyToks)=" ++ (showGhc (pn,paramPNames,modifyToks))
  -- logm $ "addParamsToDecls: decls=" ++ (SYB.showData SYB.Renamer 0 decls)
  if (paramPNames/=[])
        then mapM addParamToDecl decls
        else return decls
  where
   addParamToDecl :: GHC.LHsBind GHC.Name -> RefactGhc (GHC.LHsBind GHC.Name)
   addParamToDecl (GHC.L l1 (GHC.FunBind (GHC.L l2 pname) i (GHC.MatchGroup matches ptt) co fvs t))
    | pname == pn
    = do matches' <- mapM addParamtoMatch matches
         return (GHC.L l1 (GHC.FunBind (GHC.L l2 pname) i (GHC.MatchGroup matches' ptt) co fvs t))
      where
       -- addParamtoMatch (HsMatch loc fun pats rhs  decls)
       addParamtoMatch (GHC.L l (GHC.Match pats mtyp rhs))
        = do rhs' <- addActualParamsToRhs modifyToks pn paramPNames rhs
             let pats' = map GHC.noLoc $ map pNtoPat paramPNames
             _pats'' <- if modifyToks
               then do -- TODO: What happens if pats is []
                       -- Will only happen if there is a single match only.
                       logm $ "addParamtoMatch:l=" ++ (showGhc l)
                       if emptyList pats
                         then addFormalParams (Left l2) pats'
                         else addFormalParams (Right pats) pats'
                       return pats'

               else return pats'
             -- return (HsMatch loc  fun  (pats'++pats)  rhs' decls)
             return (GHC.L l (GHC.Match (pats'++pats) mtyp rhs'))

   -- addParamToDecl (TiDecorate.Dec (HsPatBind loc p rhs ds))
   addParamToDecl (GHC.L l1 (GHC.PatBind pat@(GHC.L _l2 (GHC.VarPat p)) rhs ty fvs t))
     | p == pn
       = do _rhs'<-addActualParamsToRhs modifyToks pn paramPNames rhs
            let pats' = map GHC.noLoc $ map pNtoPat paramPNames
            _pats'' <- if modifyToks  then do _ <- addFormalParams (Right [pat]) pats'
                                              return pats'
                                     else return pats'
            -- return (TiDecorate.Dec (HsFunBind loc [HsMatch loc (patToPNT p) pats' rhs ds]))
            return (GHC.L l1 (GHC.PatBind pat rhs ty fvs t))
   addParamToDecl x=return x


-- | Add tokens corresponding to the new parameters to the end of the
-- syntax element provided
addFormalParams
 :: Either GHC.SrcSpan [(GHC.LPat GHC.Name)] -- location: SrcSpan only
                                 -- if no existing params, else list
                                 -- of current params
 -> [(GHC.LPat GHC.Name)] -- params to add
 -> RefactGhc ()
addFormalParams place newParams
  = do
       -- logm $ "addFormalParams:(place,newParams):" ++ (SYB.showData SYB.Renamer 0 (place,newParams))
       -- newToks <- liftIO $ basicTokenise (prettyprintPatList prettyprint True newParams)
       let newStr = (prettyprintPatList prettyprint True newParams)

       case place of
         Left l@(GHC.RealSrcSpan _ss) -> do
           let newToks' = tokenise (gs2ss l) 0 False newStr
           let newToks = map markToken newToks'
           _ <- addToksAfterSpan l PlaceAdjacent newToks
           return ()
         Left ss -> error $ "addFormalParams: expecting RealSrcSpan, got:" ++ (showGhc ss)
         Right pats -> do
           let l = GHC.combineLocs (ghead "addFormalParams" pats) (glast "addFormalParams" pats)
           -- logm $ "addFormalParams:(l,pats)=" ++ (SYB.showData SYB.Renamer 0 (l,pats))
           toks <- getToksForSpan l

           let oldStr = GHC.showRichTokenStream $ rmOffsetFromToks toks
           let combinedToks = tokenise (gs2ss $ tokenSrcSpan $ ghead "addFormalParams" toks)
                                     0 False (newStr ++ " " ++ oldStr)

           _ <- putToksForSpan l combinedToks

           return ()

       -- drawTokenTree "after addFormalParams"
       -- drawTokenTreeDetailed "after addFormalParams"

-- ---------------------------------------------------------------------

addActualParamsToRhs :: (SYB.Typeable t, SYB.Data t) =>
                        Bool -> GHC.Name -> [GHC.Name] -> t -> RefactGhc t
addActualParamsToRhs modifyToks pn paramPNames rhs = do
    -- logm $ "addActualParamsToRhs:rhs=" ++ (SYB.showData SYB.Renamer 0 $ rhs)

    -- = applyTP (stop_tdTP (failTP `adhocTP` worker))

    r <- applyTP (stop_tdTPGhc (failTP `adhocTP` grhs)) rhs
    -- r <- everywhereMStaged SYB.Renamer (SYB.mkM grhs) rhs
    return r
     where

       -- |Limit the action to actual RHS elements
       grhs :: (GHC.GRHSs GHC.Name) -> RefactGhc (GHC.GRHSs GHC.Name)
       grhs (GHC.GRHSs g lb) = do
         -- logm $ "addActualParamsToRhs.grhs:g=" ++ (SYB.showData SYB.Renamer 0 g)
         g' <- everywhereMStaged SYB.Renamer (SYB.mkM worker) g
         return (GHC.GRHSs g' lb)

       worker :: (GHC.Located (GHC.HsExpr GHC.Name)) -> RefactGhc (GHC.Located (GHC.HsExpr GHC.Name))
       worker oldExp@(GHC.L l2 (GHC.HsVar pname))
        | pname == pn = do
              -- logm $ "addActualParamsToRhs:oldExp=" ++ (SYB.showData SYB.Renamer 0 oldExp)
              let newExp' = foldl addParamToExp oldExp paramPNames
              let newExp  = (GHC.L l2 (GHC.HsPar newExp'))
              -- TODO: updateToks must add a space at the end of the
              --       new exp
              if modifyToks then do _ <- updateToks oldExp newExp prettyprint False
                                    return newExp
                            else return newExp
       worker x = return x

       addParamToExp :: (GHC.LHsExpr GHC.Name) -> GHC.Name -> (GHC.LHsExpr GHC.Name)
       addParamToExp  expr param = GHC.noLoc (GHC.HsApp expr (GHC.noLoc (GHC.HsVar param)))


{-
Required end result : (sq pow) x + sumSquares xs

                (L {test/testdata/LiftToToplevel/D2.hs:6:21-46} 
                 (OpApp 

                  (L {test/testdata/LiftToToplevel/D2.hs:6:21-30} 
                   (HsApp 
                    (L {test/testdata/LiftToToplevel/D2.hs:6:21-28} 
                     (HsPar 
                      (L {test/testdata/LiftToToplevel/D2.hs:6:22-27} 
                       (HsApp 
                        (L {test/testdata/LiftToToplevel/D2.hs:6:22-23} 
                         (HsVar {Name: LiftToToplevel.D2.sq})) 
                        (L {test/testdata/LiftToToplevel/D2.hs:6:25-27} 
                         (HsVar {Name: pow})))))) 
                    (L {test/testdata/LiftToToplevel/D2.hs:6:30} 
                     (HsVar {Name: x})))) 

                  (L {test/testdata/LiftToToplevel/D2.hs:6:32} 
                   (HsVar {Name: GHC.Num.+})) {Fixity: infixl 6} 
                  (L {test/testdata/LiftToToplevel/D2.hs:6:34-46} 
                   (HsApp 
                    (L {test/testdata/LiftToToplevel/D2.hs:6:34-43} 
                     (HsVar {Name: LiftToToplevel.D2.sumSquares})) 
                    (L {test/testdata/LiftToToplevel/D2.hs:6:45-46} 
                     (HsVar {Name: xs}))))))))] 

Alternate, no parens : sq pow x + sumSquares xs

                (L {test/testdata/LiftToToplevel/D2.hs:6:21-44} 
                 (OpApp 

                  (L {test/testdata/LiftToToplevel/D2.hs:6:21-28} 
                   (HsApp 
                    (L {test/testdata/LiftToToplevel/D2.hs:6:21-26} 
                     (HsApp 
                      (L {test/testdata/LiftToToplevel/D2.hs:6:21-22} 
                       (HsVar {Name: LiftToToplevel.D2.sq})) 
                      (L {test/testdata/LiftToToplevel/D2.hs:6:24-26} 
                       (HsVar {Name: pow})))) 
                    (L {test/testdata/LiftToToplevel/D2.hs:6:28} 
                     (HsVar {Name: x})))) 


                  (L {test/testdata/LiftToToplevel/D2.hs:6:30} 
                   (HsVar {Name: GHC.Num.+})) {Fixity: infixl 6} 
                  (L {test/testdata/LiftToToplevel/D2.hs:6:32-44} 
                   (HsApp 
                    (L {test/testdata/LiftToToplevel/D2.hs:6:32-41} 
                     (HsVar {Name: LiftToToplevel.D2.sumSquares})) 
                    (L {test/testdata/LiftToToplevel/D2.hs:6:43-44} 
                     (HsVar {Name: xs}))))))))] 


Original : sq x + sumSquares xs

                (L {test/testdata/LiftToToplevel/D2.hs:6:21-40} 
                 (OpApp 

                  (L {test/testdata/LiftToToplevel/D2.hs:6:21-24} 
                   (HsApp 
                    (L {test/testdata/LiftToToplevel/D2.hs:6:21-22} 
                     (HsVar {Name: sq})) 
                    (L {test/testdata/LiftToToplevel/D2.hs:6:24} 
                     (HsVar {Name: x})))) 


                  (L {test/testdata/LiftToToplevel/D2.hs:6:26} 
                   (HsVar {Name: GHC.Num.+})) {Fixity: infixl 6} 
                  (L {test/testdata/LiftToToplevel/D2.hs:6:28-40} 
                   (HsApp 
                    (L {test/testdata/LiftToToplevel/D2.hs:6:28-37} 
                     (HsVar {Name: LiftToToplevel.D2.sumSquares})) 
                    (L {test/testdata/LiftToToplevel/D2.hs:6:39-40} 
                     (HsVar {Name: xs}))))))))] 

-}

-- ---------------------------------------------------------------------

-- | Duplicate a function\/pattern binding declaration under a new name
-- right after the original one. Also updates the token stream.
duplicateDecl::(SYB.Data t) =>
  [GHC.LHsBind GHC.Name]  -- ^ The declaration list
  ->t                     -- ^ Any signatures are in here
  ->GHC.Name              -- ^ The identifier whose definition is to be duplicated
  ->GHC.Name              -- ^ The new name (possibly qualified)
  ->RefactGhc [GHC.LHsBind GHC.Name]  -- ^ The result
duplicateDecl decls sigs n newFunName
 = do
      let Just sspan = getSrcSpan funBinding
      toks <- getToksForSpan sspan
      -- lay <- getLayoutForSpan sspan

      newSpan <- case typeSig of
        [] -> return sspan
        _  -> do
          let Just sspanSig = getSrcSpan typeSig
          toksSig <- getToksForSpan sspanSig
          -- laySig  <- getLayoutForSpan sspanSig

          let colStart  = tokenCol $ ghead "duplicateDecl.sig"
                    $ dropWhile isWhiteSpace toksSig

          typeSig'  <- putDeclToksAfterSpan sspan (ghead "duplicateDecl" typeSig) (PlaceAbsCol 2 colStart 0) toksSig
          _typeSig'' <- renamePN n newFunName True False typeSig'

          let (GHC.L sspanSig' _) = typeSig'

          return sspanSig'

      let rowOffset = case typeSig of
                        [] -> 2
                        _  -> 1

      let colStart  = tokenCol $ ghead "duplicateDecl.decl"
                    $ dropWhile isWhiteSpace toks

      funBinding'  <- putDeclToksAfterSpan newSpan (ghead "duplicateDecl" funBinding) (PlaceAbsCol rowOffset colStart 2) toks
      funBinding'' <- renamePN n newFunName True False funBinding'

      -- return (typeSig'++funBinding') -- ++AZ++ TODO: reinstate this
      return [funBinding'']
     where
       declsToDup = definingDeclsNames [n] decls True False -- ++AZ++ should recursive be set true?
       funBinding = filter isFunOrPatBindR declsToDup     --get the fun binding.
       typeSig = definingSigsNames [n] sigs

-- ---------------------------------------------------------------------

-- | Remove the declaration (and the type signature is the second
-- parameter is True) that defines the given identifier from the
-- declaration list.
rmDecl:: (SYB.Data t)
    => GHC.Name     -- ^ The identifier whose definition is to be removed.
    -> Bool         -- ^ True means including the type signature.
    -> t            -- ^ The AST fragment containting the declarations
    -> RefactGhc
        (t,
        GHC.LHsBind GHC.Name,
        Maybe (GHC.LSig GHC.Name))  -- ^ The result and the removed
                                   -- declaration, with SrcSpans
                                   -- adjusted to reflect the stashed
                                   -- tokens and the possibly removed
                                   -- siganture
rmDecl pn incSig t = do
  logm $ "rmDecl:(pn,incSig)= " ++ (showGhc (pn,incSig)) -- ++AZ++
  -- drawTokenTreeDetailed "rmDecl.entry tree" -- ++AZ++ 'in' present
  setStateStorage StorageNone
  t2  <- everywhereMStaged' SYB.Renamer (SYB.mkM inLet) t -- top down
  -- drawTokenTreeDetailed "rmDecl.entry after inLet" -- ++AZ++ 'in' missing
  -- drawTokenTree "rmDecl.entry after inLet" -- ++AZ++ 'in' missing
  t'  <- everywhereMStaged' SYB.Renamer (SYB.mkM inDecls `SYB.extM` inGRHSs) t2 -- top down

             -- applyTP (once_tdTP (failTP `adhocTP` inDecls)) t
  -- t'  <- everywhereMStaged SYB.Renamer (SYB.mkM inDecls) t
  (t'',sig') <- if incSig
                  then rmTypeSig pn t'
                  else return (t', Nothing)
  storage <- getStateStorage
  let decl' = case storage of
                StorageBind bind -> bind
                x                -> error $ "rmDecl: unexpected value in StateStorage:" ++ (show x)
  return (t'',decl',sig')
  where
    inGRHSs ((GHC.GRHSs a localDecls)::GHC.GRHSs GHC.Name)
      -- was | not $ emptyList (snd (break (defines pn) decls)) -- /=[]
      | not $ emptyList (snd (break (defines pn) (hsBinds localDecls))) -- /=[]
      = do
         let decls = hsBinds localDecls
         -- logm $ "rmDecl:inGRHSs decls=" ++ (SYB.showData SYB.Renamer 0 $ decls)
         -- logm $ "rmDecl:inGRHSs localDecls=" ++ (SYB.showData SYB.Renamer 0 $ localDecls)
         let (_decls1, decls2) = break (defines pn) decls
             decl = ghead "rmDecl" decls2
         topLevel <- isTopLevelPN pn
         decls' <- case topLevel of
                     True   -> rmTopLevelDecl decl decls
                     False  -> rmLocalDecl decl decls
         return (GHC.GRHSs a (replaceBinds localDecls decls'))
    inGRHSs x = return x

    inDecls (decls::[GHC.LHsBind GHC.Name])
      | not $ emptyList (snd (break (defines pn) decls)) -- /=[]
      = do let (_decls1, decls2) = break (defines pn) decls
               decl = ghead "rmDecl" decls2
           -- error $ (render.ppi) t -- ecl ++ (show decl)
           topLevel <- isTopLevelPN pn
           case topLevel of
                     True   -> rmTopLevelDecl decl decls
                     False  -> rmLocalDecl decl decls
    inDecls x = return x

    inLet :: GHC.LHsExpr GHC.Name -> RefactGhc (GHC.LHsExpr GHC.Name)
    inLet (GHC.L ss (GHC.HsLet localDecls expr@(GHC.L l _)))
      | not $ emptyList (snd (break (defines pn) (hsBinds localDecls)))
      = do
         -- putSrcSpan ss -- Make sure the tree includes a SrcSpan for
                          -- the HsLet, for when it is replaced later

         let decls = hsBinds localDecls
         let (decls1, decls2) = break (defines pn) decls
             decl = ghead "rmDecl" decls2

         -- drawTokenTreeDetailed "rmDecl.inLet tree" -- ++AZ++ present
         toks <- getToksForSpan l
         -- drawTokenTreeDetailed "rmDecl.inLet tree" -- ++AZ++ missing
         -- toks <- getToksForSpanWithIntros l
         removeToksForPos (getStartEndLoc decl)
         -- drawTokenTree "rmDecl.inLet after removeToksForPos"
         decl' <- syncDeclToLatestStash decl
         setStateStorage (StorageBind decl')
         -- drawTokenTree "rmDecl.inLet after syncDeclToLatestStash"
         case length decls of
           1 -> do -- Removing the last declaration
            -- logm $ "rmDecl.inLet:length decls = 1: expr=" ++ (SYB.showData SYB.Renamer 0 expr)
            -- putToksForSpan ss toks
            (_,expr') <- putDeclToksForSpan ss expr $ dropWhile (\tok -> isEmpty tok || isIn tok) toks
            -- drawTokenTree "rmDecl.inLet after putToksForSpan"
            return expr'
           _ -> do
            logm $ "rmDecl.inLet:length decls /= 1"
            -- drawTokenTreeDetailed "rmDecl.inLet tree"
            let decls2' = gtail "inLet" decls2
            return $ (GHC.L ss (GHC.HsLet (replaceBinds localDecls (decls1 ++ decls2')) expr))

    inLet x = return x


    rmTopLevelDecl :: GHC.LHsBind GHC.Name -> [GHC.LHsBind GHC.Name]
                -> RefactGhc [GHC.LHsBind GHC.Name]
    rmTopLevelDecl decl decls
      =do
          logm $ "rmTopLevelDecl:" -- ++AZ++

          removeToksForPos (getStartEndLoc decl)
          decl' <- syncDeclToLatestStash decl
          setStateStorage (StorageBind decl')

          let (decls1, decls2) = break (defines pn) decls
              decls2' = gtail "rmTopLevelDecl 1" decls2
          return $ (decls1 ++ decls2')
          -- return (decls \\ [decl])


    {- The difference between removing a top level declaration and a
       local declaration is: if the local declaration to be removed is
       the only declaration in current declaration list, then the 'where'/
       'let'/'in' enclosing this declaration should also be removed. Whereas,
       when a only top level decl is removed, the 'where' can not be removed.
    -}

    -- |Remove a location declaration that defines pn.
    rmLocalDecl :: GHC.LHsBind GHC.Name -> [GHC.LHsBind GHC.Name]
                -> RefactGhc [GHC.LHsBind GHC.Name]
    rmLocalDecl decl@(GHC.L sspan _) decls
     = do

         -- TODO: The let/in version is wrapped in a GHC.HsLet expression.
         -- The sspan of HsLet runs from the let keyword to the end of
         -- the in clause.
         -- (GHC.L l (HsLet (HsLocalBinds id) (LHsExpr id))
         -- So we must remove the tokens from the start of l to the
         -- start of the LHsExpr

         logm $ "rmLocalDecl: decls=" ++ (showGhc decls)
         -- drawTokenTreeDetailed $ "Before getToksForSpan :" ++ (show sspan) -- ++AZ++
         prevToks <- getToksBeforeSpan sspan -- Need these before
                                             -- sspan is deleted
         removeToksForPos (getStartEndLoc decl)
         decl' <- syncDeclToLatestStash decl
         setStateStorage (StorageBind decl')

         case length decls of
           1 -> do
             -- Get rid of preceding where or let token
             let startPos = getGhcLoc sspan
                  --divide the token stream.
                 (_toks1,toks2)=break (\t1->tokenPos t1 < startPos) $ reversedToks prevToks
                 --get the  'where' or 'let' token
                 rvToks1 = dropWhile (not.isWhereOrLet) toks2
                 --There must be a 'where' or 'let', so rvToks1 can not be empty.
                 whereOrLet = ghead "rmLocalDecl:whereOrLet" rvToks1
                 --drop the 'where' 'or 'let' token
                 -- rmEndPos   = tokenPosEnd $ ghead "rmLocalDecl.2" toks2
                 rmEndPos   = tokenPosEnd whereOrLet
                 rmStartPos = tokenPos whereOrLet

             -- logm $ "rmLocalDecl: where/let tokens:" ++ (show (_toks1,toks2)) -- ++AZ++ 
             logm $ "rmLocalDecl: where/let tokens are at" ++ (show (rmStartPos,rmEndPos)) -- ++AZ++ 
             removeToksForPos (rmStartPos,rmEndPos)

             return ()
           _ -> return ()

         let (decls1, decls2) = break (defines pn) decls
             decls2' = gtail "rmLocalDecl 3" decls2
         return $ (decls1 ++ decls2')

-- ---------------------------------------------------------------------

-- | Remove multiple type signatures
rmTypeSigs :: (SYB.Data t) =>
         [GHC.Name]  -- ^ The identifiers whose type signatures are to be removed.
      -> t           -- ^ The declarations
      -> RefactGhc (t,[GHC.LSig GHC.Name])
                     -- ^ The result and removed signatures, if there
                     -- were any
rmTypeSigs pns t = do
  (t',demotedSigsMaybe) <- foldM (\(tee,ds) n -> do { (tee',d) <- rmTypeSig n tee; return (tee', ds++[d])}) (t,[]) pns
  return (t',catMaybes demotedSigsMaybe)


-- | Remove the type signature that defines the given identifier's
-- type from the declaration list.
rmTypeSig :: (SYB.Data t) =>
         GHC.Name    -- ^ The identifier whose type signature is to be removed.
      -> t           -- ^ The declarations
      -> RefactGhc (t,Maybe (GHC.LSig GHC.Name))
                     -- ^ The result and removed signature, if there
                     -- was one
rmTypeSig pn t
  = do
     -- logm $ "rmTypeSig:t="  ++ (SYB.showData SYB.Renamer 0 t)

     setStateStorage StorageNone
     t' <- everywhereMStaged SYB.Renamer (SYB.mkM inSigs) t
     storage <- getStateStorage
     let sig' = case storage of
                  StorageSig sig -> Just sig
                  StorageNone    -> Nothing
                  x -> error $ "rmTypeSig: unexpected value in StateStorage:" ++ (show x)
     return (t',sig')
  where
   inSigs (sigs::[GHC.LSig GHC.Name])
      | not $ emptyList (snd (break (definesTypeSig pn) sigs)) -- /=[]
     = do
         let (decls1,decls2)= break (definesTypeSig pn) sigs
         let sig@(GHC.L sspan (GHC.TypeSig names typ)) = ghead "rmTypeSig" decls2
         if length names > 1
             then do
                 -- We have the following cases
                 -- [pn,x..], [..x,pn,y..], [..x,pn]
                 -- We must handle the commas correctly in
                 -- all cases
                 -- so [pn,x..] : take front comma
                 --    [..x,pn,y..] : take either front or back comma,
                 --                   but only one
                 --    [..x,pn] : take back comma
                 let newSig=(GHC.L sspan (GHC.TypeSig (filter (\(GHC.L _ x) -> x /= pn) names) typ))

                 toks <- getToksForSpan sspan
                 logm $ "rmTypeSig: fetched toks:" ++ (show toks) -- ++AZ++
                 let pnt = ghead "rmTypeSig" (filter (\(GHC.L _ x) -> x == pn) names)
                     (startPos1, endPos1) =
                         let (startPos1', endPos1') = getStartEndLoc pnt
                             in if gfromJust "rmTypeSig" (elemIndex pnt names) == 0
                                    then extendForwards  toks (startPos1',endPos1') isComma
                                    else extendBackwards toks (startPos1',endPos1') isComma
                     toks' = deleteToks toks startPos1 endPos1
                 void $ putToksForSpan sspan toks'

                 -- Construct the old signature, by keeping the
                 -- signature part but discarding the other names
                 let oldSig = (GHC.L sspan (GHC.TypeSig [pnt] typ))
                 sig'@(GHC.L sspan' _) <- syncDeclToLatestStash oldSig
                 let typeLoc = extendBackwards toks (getStartEndLoc typ) isDoubleColon
                 let (_,typTok,_) = splitToks typeLoc toks
                 let (_,pntTok,_) = splitToks (getStartEndLoc pnt) toks
                 void $ putToksForSpan sspan' (pntTok ++ typTok)
                 setStateStorage (StorageSig sig')


                 return (decls1++[newSig]++tail decls2)
             else do
                 removeToksForSpan sspan
                 sig' <- syncDeclToLatestStash sig
                 setStateStorage (StorageSig sig')
                 return (decls1++tail decls2)
   inSigs x = return x

{-
               [
                (L {test/testdata/LiftToToplevel/PatBindIn1.hs:15:7-14}
                 (TypeSig
                  [
                   (L {test/testdata/LiftToToplevel/PatBindIn1.hs:15:7} {Name: h})] 
                  (L {test/testdata/LiftToToplevel/PatBindIn1.hs:15:12-14}
                   (HsTyVar {Name: GHC.Types.Int})))),
                (L {test/testdata/LiftToToplevel/PatBindIn1.hs:16:7-14}
                 (TypeSig
                  [
                   (L {test/testdata/LiftToToplevel/PatBindIn1.hs:16:7} {Name: t})] 
                  (L {test/testdata/LiftToToplevel/PatBindIn1.hs:16:12-14}
                   (HsTyVar {Name: GHC.Types.Int})))),
                (L {test/testdata/LiftToToplevel/PatBindIn1.hs:17:7-22}
                 (TypeSig
                  [
                   (L {test/testdata/LiftToToplevel/PatBindIn1.hs:17:7-9} {Name: tup})] 
                  (L {test/testdata/LiftToToplevel/PatBindIn1.hs:17:14-22}
                   (HsTupleTy
                    (HsBoxedOrConstraintTuple)
                    [
                     (L {test/testdata/LiftToToplevel/PatBindIn1.hs:17:15-17}
                      (HsTyVar {Name: GHC.Types.Int})),
                     (L {test/testdata/LiftToToplevel/PatBindIn1.hs:17:19-21}
                      (HsTyVar {Name: GHC.Types.Int}))]))))]
-}

-- ---------------------------------------------------------------------


-- TODO: Is this function needed with GHC?

-- | Remove the qualifier from the given identifiers in the given syntax phrase.
rmQualifier:: (SYB.Data t)
             =>[GHC.Name]       -- ^ The identifiers.
               ->t           -- ^ The syntax phrase.
               ->RefactGhc t -- ^ The result.
rmQualifier pns t =
  -- error "undefined rmQualifier"
  everywhereMStaged SYB.Renamer (SYB.mkM rename) t
    where
     rename ((GHC.L l pn)::GHC.Located GHC.Name)
       | elem pn pns
       = do do -- toks <- fetchToks
               -- let toks' = replaceToks toks (row,col) (row,col) [mkToken Varid (row,col) s]
               let (rs,_) = break (=='.') $ reverse $ showGhc pn -- ++TODO: replace this with the appropriate formulation
                   s = reverse rs
               {- TODO: reinstate token update if required
               let (row,col) = getGhcLoc l
               let toks' = replaceToks toks (row,col) (row,col) [mkToken (GHC.ITvarid (GHC.mkFastString s)) (row,col) s]
               putToks toks' modified
               -}
               return (GHC.L l (GHC.mkInternalName (GHC.nameUnique pn) (GHC.mkVarOcc s) l))
     rename x = return  x

-- ---------------------------------------------------------------------

-- | Replace all occurences of a top level GHC.Name with a qualified version.
qualifyToplevelName :: GHC.Name -> RefactGhc ()
qualifyToplevelName n = do
    renamed <- getRefactRenamed
    -- logm $ "qualifyToplevelName:renamed=" ++ (SYB.showData SYB.Renamer 0 renamed)
    _ <- renamePN n n True True renamed
    return ()

-- ---------------------------------------------------------------------

-- | Rename each occurrences of the identifier in the given syntax
-- phrase with the new name. If the Bool parameter is True, then
-- modify both the AST and the token stream, otherwise only modify the
-- AST.
-- TODO: the syntax phrase is required to be GHC.Located, not sure how
-- to specify this without breaking the everywhereMStaged call

renamePN::(SYB.Data t)
   =>GHC.Name             -- ^ The identifier to be renamed.
   ->GHC.Name             -- ^ The new name, including possible qualifier
   ->Bool                 -- ^ True means modifying the token stream as well.
   ->Bool                 -- ^ True means use the qualified form for
                          --   the new name.
   ->t                    -- ^ The syntax phrase
   ->RefactGhc t
renamePN oldPN newName updateTokens useQual t = do
  -- = error $ "renamePN: sspan=" ++ (showGhc sspan) -- ++AZ++
  -- logm $ "renamePN': (oldPN,newName)=" ++ (showGhc (oldPN,newName))
  -- logm $ "renamePN: t=" ++ (SYB.showData SYB.Renamer 0 t)
  -- Note: bottom-up traversal
  let isRenamed = somethingStaged SYB.Renamer Nothing
                   (Nothing `SYB.mkQ` isRenamedSource `SYB.extQ` isRenamedGroup) t


  t' <- if isRenamed == (Just True)
    then
      everywhereMStaged SYB.Renamer
                 (SYB.mkM renameRenamedSource
                 `SYB.extM` renameGroup
                 ) t
    else
      renamePNworker oldPN newName updateTokens useQual t
  -- t'' <- adjustLayoutAfterRename oldPN newName t'
  return t'
  where
    isRenamedSource :: GHC.RenamedSource -> Maybe Bool
    isRenamedSource (_g,_i,_e,_d) = Just True

    isRenamedGroup :: GHC.HsGroup GHC.Name -> Maybe Bool
    isRenamedGroup _g = Just True

    -- ---------------------------------

    renameRenamedSource :: GHC.RenamedSource -> RefactGhc GHC.RenamedSource
    renameRenamedSource (g,i,e,d) = do
      i' <- renamePNworker oldPN newName updateTokens False i
      e' <- renamePNworker oldPN newName updateTokens useQual e
      return (g,i',e',d)

    renameGroup :: (GHC.HsGroup GHC.Name) -> RefactGhc (GHC.HsGroup GHC.Name)
    renameGroup  g
     = do
          logm $ "renamePN:renameGroup"
          g' <- renamePNworker oldPN newName updateTokens useQual g
          return g'
    -- renameGroup x = return x

-- ---------------------------------------------------------------------

-- | Rename each occurrences of the identifier in the given syntax
-- phrase with the new name. If the Bool parameter is True, then
-- modify both the AST and the token stream, otherwise only modify the
-- AST.
-- TODO: the syntax phrase is required to be GHC.Located, not sure how
-- to specify this without breaking the everywhereMStaged call
renamePNworker::(SYB.Data t)
   =>GHC.Name             -- ^ The identifier to be renamed.
   ->GHC.Name             -- ^ The new name, including possible qualifier
   ->Bool                 -- ^ True means modifying the token stream as well.
   ->Bool                 -- ^ True means use the qualified form for
                          --   the new name.
   ->t                    -- ^ The syntax phrase
   ->RefactGhc t
renamePNworker oldPN newName updateTokens useQual t = do
  -- logm $ "renamePN: (oldPN,newName)=" ++ (showGhc (oldPN,newName))
  -- Note: bottom-up traversal (no ' at end)
  everywhereMStaged SYB.Renamer (SYB.mkM rename
  -- everywhereMStaged' SYB.Renamer (SYB.mkM rename
                               `SYB.extM` renameVar
                               `SYB.extM` renameTyVar
                               `SYB.extM` renameHsTyVarBndr
                               `SYB.extM` renameLIE
                               `SYB.extM` renameLPat
                               `SYB.extM` renameTypeSig
                               `SYB.extM` renameFunBind
                               ) t
  where
    rename :: (GHC.Located GHC.Name) -> RefactGhc (GHC.Located GHC.Name)
    rename (GHC.L l n)
     | (GHC.nameUnique n == GHC.nameUnique oldPN)
     = do
          logm $ "renamePNworker:rename at :" ++ (show l) ++ (showSrcSpanF l)
          -- drawTokenTree "before worker" -- ++AZ++ debug
          worker useQual l Nothing
          return (GHC.L l newName)
    rename x = return x

    renameVar :: (GHC.Located (GHC.HsExpr GHC.Name)) -> RefactGhc (GHC.Located (GHC.HsExpr GHC.Name))
    renameVar v@(GHC.L l (GHC.HsVar n))
     | (GHC.nameUnique n == GHC.nameUnique oldPN)
     = do
          logm $ "renamePNworker:renameVar at :" ++ (showGhc l)

          -- Get the original qualification, if any
          rn <- (getParsedForRenamedLocated v :: RefactGhc (GHC.LHsExpr GHC.RdrName))
          let (GHC.L _ (GHC.HsVar mqn)) = rn
          let mrnq = GHC.isQual_maybe mqn
          logm $ "renamePNworker:renameVar mrn,mrnq :" ++ (showGhc (rn,mrnq))

          worker useQual l mrnq
          return (GHC.L l (GHC.HsVar newName))
    renameVar x = return x

    -- HsTyVar {Name: Renaming.D1.Tree}))
    renameTyVar :: (GHC.Located (GHC.HsType GHC.Name)) -> RefactGhc (GHC.Located (GHC.HsType GHC.Name))
    renameTyVar v@(GHC.L l (GHC.HsTyVar n))
     | (GHC.nameUnique n == GHC.nameUnique oldPN)
     = do
          logm $ "renamePNworker:renameTyVar at :" ++ (showGhc l)

          -- Get the original qualification, if any
          rn <- (getParsedForRenamedLocated v :: RefactGhc (GHC.LHsType GHC.RdrName))
          let (GHC.L _ (GHC.HsTyVar mqn)) = rn
          let mrnq = GHC.isQual_maybe mqn
          logm $ "renamePNworker:renameVar mrn,mrnq :" ++ (showGhc (rn,mrnq))

          worker useQual l mrnq
          return (GHC.L l (GHC.HsTyVar newName))
    renameTyVar x = return x


    renameHsTyVarBndr :: (GHC.LHsTyVarBndr GHC.Name) -> RefactGhc (GHC.LHsTyVarBndr GHC.Name)
#if __GLASGOW_HASKELL__ > 704
    renameHsTyVarBndr v@(GHC.L l (GHC.UserTyVar n))
#else
    renameHsTyVarBndr v@(GHC.L l (GHC.UserTyVar n typ))
#endif
     | (GHC.nameUnique n == GHC.nameUnique oldPN)
     = do
          logm $ "renamePNworker:renameHsTyVarBndr at :" ++ (showGhc l)

          -- Get the original qualification, if any
          rn <- (getParsedForRenamedLocated v :: RefactGhc (GHC.LHsTyVarBndr GHC.RdrName))
#if __GLASGOW_HASKELL__ > 704
          let (GHC.L _ (GHC.UserTyVar mqn)) = rn
#else
          let (GHC.L _ (GHC.UserTyVar mqn _)) = rn
#endif
          let mrnq = GHC.isQual_maybe mqn
          logm $ "renamePNworker:renameVar mrn,mrnq :" ++ (showGhc (rn,mrnq))

          worker useQual l mrnq
#if __GLASGOW_HASKELL__ > 704
          return (GHC.L l (GHC.UserTyVar newName))
#else
          return (GHC.L l (GHC.UserTyVar newName typ))
#endif
    renameHsTyVarBndr x = return x

    -- ---------------------------------

    renameLIE :: (GHC.LIE GHC.Name) -> RefactGhc (GHC.LIE GHC.Name)
    renameLIE (GHC.L l (GHC.IEVar n))
     | (GHC.nameUnique n == GHC.nameUnique oldPN)
     = do
          -- logm $ "renamePNworker:renameLIE.IEVar at :" ++ (showGhc l)
          worker useQual l Nothing
          return (GHC.L l (GHC.IEVar newName))

    renameLIE (GHC.L l (GHC.IEThingAbs n))
     | (GHC.nameUnique n == GHC.nameUnique oldPN)
     = do
          -- logm $ "renamePNworker:renameLIE.IEThingAbs at :" ++ (showGhc l)
          worker useQual l Nothing
          return (GHC.L l (GHC.IEThingAbs newName))

    renameLIE (GHC.L l (GHC.IEThingAll n))
     | (GHC.nameUnique n == GHC.nameUnique oldPN)
     = do
          -- logm $ "renamePNworker:renameLIE.IEThingAll at :" ++ (showGhc l)
          worker useQual l Nothing
          return (GHC.L l (GHC.IEThingAll newName))

    -- TODO: check inside the ns here too
    renameLIE (GHC.L l (GHC.IEThingWith n ns))
     | (GHC.nameUnique n == GHC.nameUnique oldPN)
     = do
          logm $ "renamePNworker:renameLIE.IEThingWith at :" ++ (showGhc l)
          worker useQual l Nothing
          return (GHC.L l (GHC.IEThingWith newName ns))
     | any (\nn -> (GHC.nameUnique nn == GHC.nameUnique oldPN)) ns
     = do
          -- We have to find the right token, no locations to help
          toks <- getToksForSpan l
          -- find the opening parenthesis
          let (_,pt) = break isOpenParen $ filter (not . isWhiteSpaceOrIgnored) toks
          -- logm $ "renamePNworker:renameLIE.IEThingWith ns pt=" ++ (show pt)
          let nstoks = gtail "renamePNworker" pt
          let unQualOld = (GHC.occNameString $ GHC.getOccName oldPN)
          -- logm $ "renamePNworker:renameLIE.IEThingWith unquaOld=" ++ (show unQualOld)
          let _tok@(GHC.L lt _,_) = ghead "renamePNworker" $ filter (\tt -> tokenCon tt == showGhc oldPN || tokenCon tt == unQualOld) nstoks
          -- logm $ "renamePNworker:renameLIE.IEThingWith ns tok=" ++ (show _tok)
          logm $ "renamePNworker:renameLIE.IEThingWith ns at :" ++ (showGhc lt)
          worker useQual lt Nothing
          -- TODO: update ns
          return (GHC.L l (GHC.IEThingWith newName ns))

    renameLIE x = do
         -- logm $ "renamePNworker:renameLIE miss for :" ++ (showGhc x)
         return x

    -- ---------------------------------


    renameLPat :: (GHC.LPat GHC.Name) -> RefactGhc (GHC.LPat GHC.Name)
    renameLPat v@(GHC.L l (GHC.VarPat n))
     | (GHC.nameUnique n == GHC.nameUnique oldPN)
     = do
          logm $ "renamePNworker:renameLPat at :" ++ (showGhc l)

          -- Get the original qualification, if any
          rn <- (getParsedForRenamedLocated v :: RefactGhc (GHC.LPat GHC.RdrName))
          let (GHC.L _ (GHC.VarPat mqn)) = rn
          let mrnq = GHC.isQual_maybe mqn
          logm $ "renamePNworker:renameVar mrn,mrnq :" ++ (showGhc (rn,mrnq))

          worker False l mrnq
          return (GHC.L l (GHC.VarPat newName))
    renameLPat x = return x

    renameFunBind :: (GHC.LHsBindLR GHC.Name GHC.Name) -> RefactGhc (GHC.LHsBindLR GHC.Name GHC.Name)
    renameFunBind (GHC.L l (GHC.FunBind (GHC.L ln n) fi (GHC.MatchGroup matches typ) co fvs tick))
     | (GHC.nameUnique n == GHC.nameUnique oldPN) || (GHC.nameUnique n == GHC.nameUnique newName)
     = do -- Need to (a) rename the actual funbind name
          --         NOTE: due to bottom-up traversal, (a) should
          --               already have been done.
          --         (b) rename each of 'tail matches'
          --             (head is renamed in (a) )
          -- logm $ "renamePNWorker.renameFunBind"
          worker False ln Nothing
          -- Now do (b)
          logm $ "renamePNWorker.renameFunBind.renameFunBind:starting matches"
          let w (GHC.L lm _match) = worker False lm' Nothing
               where
                ((GHC.L lm' _),_) = newNameTok False lm oldPN
          mapM_ w $ tail matches
          logm $ "renamePNWorker.renameFunBind.renameFunBind.renameFunBind:matches done"
          return (GHC.L l (GHC.FunBind (GHC.L ln newName) fi (GHC.MatchGroup matches typ) co fvs tick))
    renameFunBind x = return x

    renameTypeSig :: (GHC.LSig GHC.Name) -> RefactGhc (GHC.LSig GHC.Name)
    renameTypeSig (GHC.L l (GHC.TypeSig ns typ))
     = do
         -- logm $ "renamePNWorker:renameTypeSig"
         _ns' <- renamePN oldPN newName updateTokens False ns
         -- Has already been renamed, make sure qualifier is removed
         ns' <- renamePN newName newName updateTokens False ns
         typ' <- renamePN oldPN newName updateTokens False typ
         -- logm $ "renamePNWorker:renameTypeSig done"
         return (GHC.L l (GHC.TypeSig ns' typ'))
    renameTypeSig x = return x

    -- The param l is only useful for the start of the token pos
    worker :: Bool -> GHC.SrcSpan -> Maybe (GHC.ModuleName, GHC.OccName) -> RefactGhc ()
    worker useQual' l mmo
     = do if updateTokens
           then do
             newTok <- case mmo of
                   Nothing -> return $ newNameTok useQual' l newName
                   Just (modu,_) -> do
                     newName' <- mkNewGhcName (Just $ GHC.mkModule GHC.mainPackageId modu) (GHC.occNameString $ GHC.getOccName newName)
                     return $ newNameTok True l newName'
             -- replaceToken l (markToken $ newNameTok useQual' l newName)
             replaceToken l (markToken $ newTok)
             return ()
           else return ()

----------------------------------------------------------------------------------------
-- | Check whether the specified identifier is declared in the given syntax phrase t,
-- if so, rename the identifier by creating a new name automatically. If the Bool parameter 
-- is True, the token stream will be modified, otherwise only the AST is modified. 

autoRenameLocalVar:: (HsValBinds t)
                    =>Bool          -- ^ True means modfiying the token stream as well.  
                     ->GHC.Name     -- ^ The identifier.
                     ->t            -- ^ The syntax phrase.
                     -> RefactGhc t -- ^ The result.
autoRenameLocalVar modifyToks pn t = do
  logm $ "autoRenameLocalVar: (modifyToks,pn)=" ++ (showGhc (modifyToks,pn))
  -- = everywhereMStaged SYB.Renamer (SYB.mkM renameInMatch)
  if isDeclaredIn pn t
         then do t' <- worker t
                 return t'
         else do return t

      where
         worker tt =do (f,d) <- hsFDNamesFromInside tt
                       ds <- hsVisibleNames pn (hsValBinds tt)
                       let newNameStr=mkNewName (nameToString pn) (nub (f `union` d `union` ds)) 1
                       newName <- mkNewGhcName Nothing newNameStr
                       if modifyToks
                         then renamePN pn newName True False tt
                         else renamePN pn newName False False tt

-- ---------------------------------------------------------------------

-- | Show a list of entities, the parameter f is a function that
-- specifies how to format an entity.
showEntities:: (t->String) -> [t] ->String
showEntities _ [] = ""
showEntities f [pn] = f pn
showEntities f (pn:pns) =f pn ++ "," ++ showEntities f pns


-- ---------------------------------------------------------------------

isMainModule :: GHC.Module -> Bool
isMainModule modu = GHC.modulePackageId modu == GHC.mainPackageId

-- ---------------------------------------------------------------------

-- | Return the identifier's defining location.
-- defineLoc::PNT->SrcLoc
defineLoc :: GHC.Located GHC.Name -> GHC.SrcLoc
defineLoc (GHC.L _ name) = GHC.nameSrcLoc name

-- | Return the identifier's source location.
-- useLoc::PNT->SrcLoc
useLoc:: (GHC.Located GHC.Name) -> GHC.SrcLoc
-- useLoc (GHC.L l _) = getGhcLoc l
useLoc (GHC.L l _) = GHC.srcSpanStart l

-- ---------------------------------------------------------------------

-- | Return True if the identifier is used in the RHS if a
-- function\/pattern binding.
isUsedInRhs::(SYB.Data t) => (GHC.Located GHC.Name) -> t -> Bool
isUsedInRhs pnt t = useLoc pnt /= defineLoc pnt  && not (notInLhs)
  where
    notInLhs = fromMaybe False $ somethingStaged SYB.Parser Nothing
            (Nothing `SYB.mkQ` inMatch `SYB.extQ` inDecl) t
     where
      inMatch ((GHC.FunBind name _ (GHC.MatchGroup _matches _) _ _ _) :: GHC.HsBind t)
         | isJust (find (sameOccurrence pnt) [name]) = Just True
      inMatch _ = Nothing

      inDecl ((GHC.TypeSig is _) :: GHC.Sig t)
        |isJust (find (sameOccurrence pnt) is)   = Just True
      inDecl _ = Nothing

-- ---------------------------------------------------------------------
-- | Find all occurrences with location of the given name
findAllNameOccurences :: (SYB.Data t) => GHC.Name -> t -> [(GHC.Located GHC.Name)]
findAllNameOccurences  name t
  = res
       where
        res = SYB.everythingStaged SYB.Renamer (++) []
            ([] `SYB.mkQ` worker `SYB.extQ` workerBind `SYB.extQ` workerExpr) t

        worker (ln@(GHC.L _l n) :: (GHC.Located GHC.Name))
          | GHC.nameUnique n == GHC.nameUnique name = [ln]
        worker _ = []

        workerBind (GHC.L l (GHC.VarPat n) :: (GHC.Located (GHC.Pat GHC.Name)))
          | GHC.nameUnique n == GHC.nameUnique name  = [(GHC.L l n)]
        workerBind _ = []

        workerExpr (GHC.L l (GHC.HsVar n) :: (GHC.Located (GHC.HsExpr GHC.Name)))
          | GHC.nameUnique n == GHC.nameUnique name  = [(GHC.L l n)]
        workerExpr _ = []

-- ---------------------------------------------------------------------

-- | Return True if the identifier occurs in the given syntax phrase.
findPNT::(SYB.Data t) => GHC.Located GHC.Name -> t -> Bool
findPNT (GHC.L _ pn) = findPN pn

-- | Return True if the identifier occurs in the given syntax phrase.
findPN::(SYB.Data t)=> GHC.Name -> t -> Bool
findPN pn
   = isJust.somethingStaged SYB.Parser Nothing (Nothing `SYB.mkQ` worker)
     where
        worker (n::GHC.Name)
           | GHC.nameUnique pn == GHC.nameUnique n = Just True
        worker _ = Nothing

-- | Return True if any of the specified PNames ocuur in the given syntax phrase.
findPNs::(SYB.Data t)=> [GHC.Name] -> t -> Bool
findPNs pns
   = isJust.somethingStaged SYB.Parser Nothing (Nothing `SYB.mkQ` worker)
     where
        uns = map GHC.nameUnique pns

        worker (n::GHC.Name)
           | elem (GHC.nameUnique n) uns = Just True
        worker _ = Nothing

-- | Return the type checked `GHC.Id` corresponding to the given
-- `GHC.Name`

-- TODO: there has to be a simpler way, using the appropriate GHC internals
findIdForName :: GHC.Name -> RefactGhc (Maybe GHC.Id)
findIdForName n = do
  tm <- getTypecheckedModule
  let t = GHC.tm_typechecked_source tm
  let r = somethingStaged SYB.Parser Nothing (Nothing `SYB.mkQ` worker) t
      worker (i::GHC.Id)
         | (GHC.nameUnique n) ==  (GHC.varUnique i) = Just i
      worker _ = Nothing
  return r

-- ---------------------------------------------------------------------

getTypeForName :: GHC.Name -> RefactGhc (Maybe GHC.Type)
getTypeForName n = do
  mId <-  findIdForName n
  case mId of
    Nothing -> return Nothing
    Just i -> return $ Just (GHC.varType i)

-- ---------------------------------------------------------------------

-- | Given the syntax phrase, find the largest-leftmost expression
-- contained in the region specified by the start and end position, if
-- found.
locToExp:: (SYB.Data t,SYB.Typeable n) =>
                   SimpPos    -- ^ The start position.
                -> SimpPos    -- ^ The end position.
                -> t          -- ^ The syntax phrase.
                -> Maybe (GHC.Located (GHC.HsExpr n)) -- ^ The result.
locToExp beginPos endPos t = res
  where
     res = somethingStaged SYB.Parser Nothing (Nothing `SYB.mkQ` expr) t

     expr :: GHC.Located (GHC.HsExpr n) -> (Maybe (GHC.Located (GHC.HsExpr n)))
     expr e
        |inScope e = Just e
     expr _ = Nothing

     inScope :: GHC.Located e -> Bool
     inScope (GHC.L l _) =
       let
         (startLoc,endLoc) = case l of
           (GHC.RealSrcSpan ss) ->
             ((GHC.srcSpanStartLine ss,GHC.srcSpanStartCol ss),
              (GHC.srcSpanEndLine ss,GHC.srcSpanEndCol ss))
           (GHC.UnhelpfulSpan _) -> ((0,0),(0,0))
       in
        (startLoc>=beginPos) && (startLoc<= endPos) && (endLoc>= beginPos) && (endLoc<=endPos)

--------------------------------------------------------------------------------


ghcToPN :: GHC.RdrName -> PName
ghcToPN rdr = PN rdr

lghcToPN :: GHC.Located GHC.RdrName -> PName
lghcToPN (GHC.L _ rdr) = PN rdr


-- | If an expression consists of only one identifier then return this
-- identifier in the GHC.Name format, otherwise return the default Name
expToName:: GHC.Located (GHC.HsExpr GHC.Name) -> GHC.Name
expToName (GHC.L _ (GHC.HsVar pnt)) = pnt
expToName (GHC.L _ (GHC.HsPar e))   = expToName e
expToName _ = defaultName


nameToString :: GHC.Name -> String
nameToString name = showGhc name

-- | If a pattern consists of only one identifier then return this
-- identifier, otherwise return Nothing
patToPNT::GHC.LPat GHC.Name -> Maybe GHC.Name
patToPNT (GHC.L _ (GHC.VarPat n)) = Just n
patToPNT _ = Nothing


-- | Compose a pattern from a pName.
pNtoPat :: GHC.Name -> GHC.Pat GHC.Name
pNtoPat pname = GHC.VarPat pname
    -- =let loc=srcLoc pname
    --  in (TiDecorate.Pat (HsPId (HsVar (PNT pname Value (N (Just loc))))))

-- ---------------------------------------------------------------------

-- TODO: This should use the TokenUtils API
getToksForDecl :: SYB.Data t =>
  t -> [PosToken] -> [PosToken]
getToksForDecl decl toks
      = let (startPos, endPos) = startEndLocIncComments toks decl
            (toks1, _) =let(ts1,(_t:ts2'))= break (\t -> tokenPos t >= endPos) toks
                        in (ts1, ts2')
        in dropWhile (\t -> tokenPos t < startPos {- was || isNewLn t -}) toks1

-- ---------------------------------------------------------------------

-- TODO: this is currently only used in a test
-- Get the toks for a declaration, and adjust its offset to 0.
getDeclAndToks :: (HsValBinds t)
     => GHC.Name -> Bool -> [PosToken] -> t
     -> ([GHC.LHsBind GHC.Name],[PosToken])
getDeclAndToks pn _incSig toks t =
  let
    decls     = definingDeclsNames [pn] (hsBinds t) True True
    declToks  = getToksForDecl decls toks

  in (decls, removeToksOffset declToks)

-- ---------------------------------------------------------------------

-- TODO: this is currently only used in a test
-- | Get the signature and tokens for a declaration
getSigAndToks :: (SYB.Data t) => GHC.Name -> t -> [PosToken]
     -> Maybe (GHC.LSig GHC.Name,[PosToken])
getSigAndToks pn t toks
  = case (getSig pn t) of
      Nothing -> Nothing
      Just sig -> Just (sig, removeToksOffset $ getToksForDecl sig toks)


-- ---------------------------------------------------------------------

-- | Normalise a set of tokens to start at the offset of the first one
removeToksOffset :: [PosToken] -> [PosToken]
removeToksOffset toks = toks'
  where
    toks' = case toks of
              [] -> []
              _  -> removeOffset offset toks
                      where
                        (_r,c) = tokenPos $ head toks
                        offset = c -- getIndentOffset toks (r+1,c)

-- ---------------------------------------------------------------------

-- | Remove at most `offset` whitespaces from each line in the tokens

-- TODO: move this function to LocUtils.hs
-- TODO: add a test for this
removeOffset :: Int -> [PosToken] -> [PosToken]
-- removeOffset offset toks = error $ "removeOffset:offset=" ++ (show offset) -- ++AZ++
removeOffset offset toks = map (\(t,s) -> (adjust t,s)) toks
  where
    adjust (GHC.L l t) = (GHC.L l' t)
      where
        l' =  case l of
          GHC.RealSrcSpan ss ->
            let
              locs = GHC.mkSrcLoc (GHC.srcSpanFile ss) (GHC.srcSpanStartLine ss) ((GHC.srcSpanStartCol ss) - offset)
              loce = GHC.mkSrcLoc (GHC.srcSpanFile ss) (GHC.srcSpanEndLine ss) ((GHC.srcSpanEndCol ss) - offset)
              -- loc = GHC.mkSrcLoc (GHC.srcSpanFile ss) (1 + GHC.srcSpanEndLine ss) 0
            in
              GHC.mkSrcSpan locs loce
          _ -> l

-- ---------------------------------------------------------------------

-- | Get signature for a declaration
getSig :: (SYB.Data t) => GHC.Name -> t
     -> Maybe (GHC.LSig GHC.Name)
getSig pn t = maybeSig
  where
   maybeSig = if (emptyList sigList)
      then Nothing
      else Just $ head sigList

   sigList = SYB.everythingStaged SYB.Renamer (++) []
              ([] `SYB.mkQ` inDecls) t

   inDecls (sigs::[GHC.LSig GHC.Name])
      | not $ emptyList (snd (break (definesTypeSig pn) sigs)) -- /=[]
     = let (_decls1,decls2)= break (definesTypeSig pn) sigs
           sig@(GHC.L l (GHC.TypeSig names typ)) = ghead "getSigsAndToks" decls2  -- as decls2/=[], no problem with head
           sig' = if  length names > 1
                   then (GHC.L l (GHC.TypeSig (filter (\(GHC.L _ x) -> x /= pn) names) typ))
                   else sig
       in [sig']
   inDecls _ = []

-- ---------------------------------------------------------------------


