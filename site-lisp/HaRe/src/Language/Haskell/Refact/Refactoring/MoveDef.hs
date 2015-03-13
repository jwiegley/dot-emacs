{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.Haskell.Refact.Refactoring.MoveDef
  ( liftToTopLevel
  , liftOneLevel
  , demote
  -- ,liftingInClientMod
  ) where

import qualified Data.Generics as SYB
import qualified GHC.SYB.Utils as SYB

-- import qualified DynFlags      as GHC
import qualified Exception             as GHC
import qualified FastString            as GHC
import qualified GHC                   as GHC
import qualified Name                  as GHC
import qualified Outputable            as GHC
import qualified TyCon                 as GHC
import qualified TypeRep               as GHC
import qualified Var                   as Var

import Control.Exception
import Control.Monad.State
import qualified Data.Generics.Zipper as Z
import Data.List
import Data.Maybe

import Language.Haskell.GhcMod
import Language.Haskell.Refact.API

import Data.Generics.Strafunski.StrategyLib.StrategyLib

-- import Debug.Trace

-- ---------------------------------------------------------------------

-- data Direction = UptoTopLevel | UpOneLevel | Down

{--------This function handles refactorings involving moving a definition--------

 According to the Haskell's syntax, a declaration may occur in one of
the following six contexts:

  1. A top level declaration in the module:
        old: HsModule SrcLoc ModuleName (Maybe [HsExportSpecI i]) [HsImportDeclI i] ds
        new: (HsGroup Name, [LImportDecl Name], Maybe [LIE Name], Maybe LHsDocString)
              HsGroup hs_valds :: HsValBinds id ...

  2. A local declaration in a Match: (of a FunBind)
        old: HsMatch SrcLoc i [p] (HsRhs e) ds
        new: Match [LPat id] (Maybe (LHsType id)) (GRHSs id)

  3. A local declaration in a pattern binding:
        old: HsPatBind SrcLoc p (HsRhs e) ds
        new: PatBind (LPat idL) (GRHSs idR) PostTcType NameSet (Maybe tickish)

  4. A local declaration in a Let expression:
        old: HsLet ds e
        new: HsLet (HsLocalBinds id) (LHsExpr id)

  5. A local declaration in a Case alternative:
        old: HsAlt SrcLoc p (HsRhs e) ds
        new: HsCase (LHsExpr id) (MatchGroup id)
           new is same as in a FunBind.

  6. A local declaration in a Do statement:
        old: HsLetStmt ds (HsStmt e p ds)
        new: LetStmt (HsLocalBindsLR idL idR)
             in context GRHS [LStmt id] (LHsExpr id)
-}

-- | Lift a definition to the top level
liftToTopLevel :: RefactSettings -> Cradle -> FilePath -> SimpPos -> IO [FilePath]
liftToTopLevel settings cradle fileName (row,col) =
  runRefacSession settings cradle (compLiftToTopLevel fileName (row,col))


compLiftToTopLevel :: FilePath -> SimpPos
     -> RefactGhc [ApplyRefacResult]
compLiftToTopLevel fileName (row,col) = do
      getModuleGhc fileName
      renamed <- getRefactRenamed
      parsed  <- getRefactParsed

      let (Just (modName,_)) = getModuleName parsed
      let maybePn = locToName (row, col) renamed
      case maybePn of
        Just pn ->  do
            liftToTopLevel' modName pn
        _       ->  error "\nInvalid cursor position!\n"


-- ---------------------------------------------------------------------

-- | Move a definition one level up from where it is now
liftOneLevel :: RefactSettings -> Cradle -> FilePath -> SimpPos -> IO [FilePath]
liftOneLevel settings cradle fileName (row,col) =
  runRefacSession settings cradle (compLiftOneLevel fileName (row,col))


compLiftOneLevel :: FilePath -> SimpPos
     -> RefactGhc [ApplyRefacResult]
compLiftOneLevel fileName (row,col) = do
      getModuleGhc fileName
      renamed <- getRefactRenamed
      parsed  <- getRefactParsed

      -- logm $ "compLiftOneLevel:(fileName,row,col)="++(show (fileName,row,col))
      -- logm $ "compLiftOneLevel:renamed=" ++ (SYB.showData SYB.Renamer 0 renamed) -- ++AZ++

      let (Just (modName,_)) = getModuleName parsed
      let maybePn = locToName (row, col) renamed
      case maybePn of
        Just pn ->  do
            rs <- liftOneLevel' modName pn
            logm $ "compLiftOneLevel:rs=" ++ (show $ (refactDone rs,map (\((_,d),_) -> d) rs))
            if (refactDone rs)
              then return rs
              else error ( "Lifting this definition failed. "++
                       " This might be because that the definition to be "++
                       "lifted is defined in a class/instance declaration.")
        _       ->  error "\nInvalid cursor position!\n"



-- ---------------------------------------------------------------------

-- | Move a definition one level down
demote :: RefactSettings -> Cradle -> FilePath -> SimpPos -> IO [FilePath]
demote settings cradle fileName (row,col) =
  runRefacSession settings cradle (compDemote fileName (row,col))

compDemote ::FilePath -> SimpPos
         -> RefactGhc [ApplyRefacResult]
compDemote fileName (row,col) = do
      getModuleGhc fileName
      renamed <- getRefactRenamed
      parsed  <- getRefactParsed

      -- TODO: make the next one an API call, that also gets the
      -- parsed source
      let (Just (modName,_)) = getModuleName parsed
      let maybePn = locToName (row, col) renamed
      case maybePn of
        Just pn -> do
          demote' modName pn
        _       -> error "\nInvalid cursor position!\n"


{-
demote args
 = do let  fileName = ghead "filename"  args
           row = read (args!!1)::Int
           col = read (args!!2)::Int
      modName <- fileNameToModName fileName
      (inscps, _, mod, toks) <- parseSourceFile fileName
      let pnt = locToPNT fileName (row, col) mod
          pn = pNTtoPN pnt
      if pn /= defaultPN
         then demote' modName fileName (mod, toks) pn
         else error "\nInvalid cursor position!\n"

move direction args
  = do let fileName = ghead "filename"  args
           row = read (args!!1)::Int
           col = read (args!!2)::Int
       modName <- fileNameToModName fileName
       (inscps, _, mod, toks) <- parseSourceFile fileName
       let pnt = locToPNT fileName (row, col) mod
           pn = pNTtoPN pnt
       if pn /= defaultPN
         then
          case direction  of
               UptoTopLevel ->liftToTopLevel' modName fileName (inscps, mod, toks) pnt
               UpOneLevel   ->liftOneLevel'   modName fileName (inscps, mod, toks) pnt
               Down         ->demote'         modName fileName (mod, toks)  pn
          else error "\nInvalid cursor position!\n"


{- Refactoring Names: 'liftToTopLevel'

   This refactoring lifts a local function/pattern binding to the top
   level of the module, so as to make it accessible to other functions in
   the current module, and those modules that import current module.

   In the current implementation, a definition will be lifted only if
   none of the identifiers defined in this definition will cause name
   clash/capture problems in the current module after lifting.

   In the case that the whole current module is exported implicitly,
   the lifted identifier will be exported automatically after lifting. If
   the identifier will cause name clash/ambiguous occurrence problem in a
   client module, it will be hided in the import declaration of the
   client module (Note: this might not be the best solution, we prefer
   hiding it in the server module instead of in the client module in the
   final version).

   In the case of indirect importing, it might be time-consuming to
   trace whether the lifted identifier will cause any problem in a client
   module that indirectly imports the current module. The current
   solution is: suppose a defintion is lifted to top level in module A,
   and module A is imported and exported by module B, then the lifted
   identifier will be hided in the import declaration of B no matter
  whether it causes problems in module B or not.

   Function name: liftToTopLevel
   parameters: fileName--current file name.
               mod -- the scoped abstract syntax tree of the module.
               pn  -- the function/pattern name to be lifted.
-}

-}

liftToTopLevel' :: GHC.ModuleName -- -> (ParseResult,[PosToken]) -> FilePath
                -> GHC.Located GHC.Name
                -> RefactGhc [ApplyRefacResult]
liftToTopLevel' modName pn@(GHC.L _ n) = do
  renamed <- getRefactRenamed
  -- logm $ "liftToTopLevel':renamed=" ++ (SYB.showData SYB.Renamer 0 renamed) -- ++AZ++
  logm $ "liftToTopLevel':pn=" ++ (showGhc pn)
  if isLocalFunOrPatName n renamed
      then do
              (refactoredMod,declPns) <- applyRefac (liftToMod) RSAlreadyLoaded

              logm $ "liftToTopLevel' applyRefac done "
              -- logm $ "liftToTopLevel' applyRefac done:toks= " ++ (show (fst $ snd refactoredMod))

              if modIsExported modName renamed
               then do clients <- clientModsAndFiles modName
                       logm $ "liftToTopLevel':(clients,declPns)=" ++ (showGhc (clients,declPns))
                       refactoredClients <- mapM (liftingInClientMod modName declPns) clients
                       return (refactoredMod:(concat refactoredClients))
               else do return [refactoredMod]
      else error "\nThe identifier is not a local function/pattern name!"

    where
       {-step1: divide the module's top level declaration list into three parts:
         'parent' is the top level declaration containing the lifted declaration,
         'before' and `after` are those declarations before and after 'parent'.
         step2: get the declarations to be lifted from parent, bind it to liftedDecls 
         step3: remove the lifted declarations from parent and extra arguments may be introduce.
         step4. test whether there are any names need to be renamed.
       -}
       liftToMod = do
         renamed <- getRefactRenamed
         let declsr = hsBinds renamed
         let (before,parent,after) = divideDecls declsr pn
         -- error ("liftToMod:(before,parent,after)=" ++ (showGhc (before,parent,after))) -- ++AZ++
         {- ++AZ++ : hsBinds does not return class or instance definitions
         when (isClassDecl $ ghead "liftToMod" parent)
               $ error "Sorry, the refactorer cannot lift a definition from a class declaration!"
         when (isInstDecl $ ghead "liftToMod" parent)
               $ error "Sorry, the refactorer cannot lift a definition from an instance declaration!"
         -}
         let liftedDecls = definingDeclsNames [n] parent True True
             declaredPns = nub $ concatMap definedPNs liftedDecls
             liftedSigs = definingSigsNames [n] parent
             mLiftedSigs = listToMaybe liftedSigs

         -- TODO: what about declarations between this
         -- one and the top level that are used in this one?

         -- logm $ "liftToMod:(liftedDecls,declaredPns)=" ++ (showGhc (liftedDecls,declaredPns))
         -- original : pns<-pnsNeedRenaming inscps mod parent liftedDecls declaredPns
         pns <- pnsNeedRenaming renamed parent liftedDecls declaredPns

         -- (_,dd) <- hsFreeAndDeclaredPNs renamed
         let dd = getDeclaredVars $ hsBinds renamed
         logm $ "liftToMod:(ddd)=" ++ (showGhc dd)

         -- drawTokenTree "liftToMod.a"
         drawTokenTreeDetailed "liftToMod.a"

         if pns==[]
           then do
             -- TODO: change the order, first move the decls then add params,
             --       else the liftedDecls get mangled while still in the parent
             (parent',liftedDecls',_mLiftedSigs') <- addParamsToParentAndLiftedDecl n dd parent liftedDecls mLiftedSigs
             -- let liftedDecls''=if paramAdded then filter isFunOrPatBindR liftedDecls'
             --                                 else liftedDecls'

             -- drawTokenTree "liftToMod.c"
             -- logm $ "liftToMod:(declaredPns)=" ++ (showGhc declaredPns)
             -- logm $ "liftToMod:(liftedDecls')=" ++ (showGhc liftedDecls')

             let renamed' = replaceBinds renamed (before++parent'++after)
                 defName  = (ghead "liftToMod" (definedPNs (ghead "liftToMod2" parent')))
             void $ moveDecl1 renamed'
                    (Just defName)
                    [GHC.unLoc pn] (Just liftedDecls') declaredPns True

             -- drawTokenTree "liftToMod.b"

             return declaredPns

           else askRenamingMsg pns "lifting"



-- ---------------------------------------------------------------------

moveDecl1 :: (HsValBinds t)
  => t -- ^ The syntax element to update
  -> Maybe GHC.Name -- ^ If specified, add defn after this one

     -- TODO: make this next parameter a single value, not a list,
     -- after module complete
  -> [GHC.Name]     -- ^ The first one is the decl to move
  -> Maybe [GHC.LHsBind GHC.Name]
  -> [GHC.Name]     -- ^ The signatures to remove. May be multiple if
                    --   decl being moved has a patbind.
  -> Bool           -- ^ True if moving to the top level
  -> RefactGhc t    -- ^ The updated syntax element (and tokens in monad)
moveDecl1 t defName ns mliftedDecls sigNames topLevel = do

  -- TODO: work with all of ns, not just the first
  let n = ghead "moveDecl1" ns
  let funBinding = case mliftedDecls of
        Nothing -> definingDeclsNames' [n] t
        Just liftedDecls -> liftedDecls

  let Just sspan = getSrcSpan funBinding
  funToks <- getToksForSpan sspan

  (t'',sigsRemoved) <- rmTypeSigs sigNames t
  (t',_declRemoved,_sigRemoved)  <- rmDecl (ghead "moveDecl3.1"  ns) False t''

  let getToksForMaybeSig (GHC.L ss _) =
                       do
                         sigToks <- getToksForSpan ss
                         return sigToks

  maybeToksSigMulti <- mapM getToksForMaybeSig
                       $ sortBy (\(GHC.L s1 _) (GHC.L s2 _) -> compare (ghcSrcSpanToForestSpan s1) (ghcSrcSpanToForestSpan s2))
                          sigsRemoved
  let maybeToksSig = concat maybeToksSigMulti

  r <- addDecl t' defName (ghead "moveDecl1 2" funBinding,sigsRemoved,Just (maybeToksSig ++ funToks)) topLevel

  return r


askRenamingMsg :: [GHC.Name] -> String -> t
askRenamingMsg pns str
  = error ("The identifier(s): " ++ (intercalate "," $ map showPN pns) ++
           " will cause name clash/capture or ambiguity occurrence problem after "
           ++ str ++", please do renaming first!")

  where
    showPN pn = showGhc (pn,GHC.nameSrcLoc pn)

-- |Get the subset of 'pns' that need to be renamed before lifting.
pnsNeedRenaming :: (SYB.Data t1) =>
  t1 -> [GHC.LHsBind GHC.Name] -> t2 -> [GHC.Name]
  -> RefactGhc [GHC.Name]
pnsNeedRenaming dest parent _liftedDecls pns
   =do
       r <- mapM pnsNeedRenaming' pns
       return (concat r)
  where
     pnsNeedRenaming' pn
       = do
            (f,d) <- hsFDsFromInside dest --f: free variable names that may be shadowed by pn
                                             --d: declaread variables names that may clash with pn
            vs <- hsVisiblePNs pn parent  --vs: declarad variables that may shadow pn
            let -- inscpNames = map (\(x,_,_,_)->x) $ inScopeInfo inscps
                vars = map pNtoName (nub (f `union` d `union` vs) \\ [pn]) -- `union` inscpNames
            -- if elem (pNtoName pn) vars  || isInScopeAndUnqualified (pNtoName pn) inscps && findEntity pn dest
            isInScope <- isInScopeAndUnqualifiedGhc (pNtoName pn) Nothing
            logm $ "MoveDef.pnsNeedRenaming:(f,d,vs,vars,isInScope)=" ++ (showGhc (f,d,vs,vars,isInScope))
            if elem (pNtoName pn) vars  || isInScope && findEntity pn dest
               then return [pn]
               else return []
     --This pNtoName takes into account the qualifier.
     pNtoName = showGhc


addParamsToParent :: (HsValBinds t) => GHC.Name -> [GHC.Name] -> t -> RefactGhc t
addParamsToParent _pn [] t = return t
addParamsToParent  pn params t = do
  logm $ "addParamsToParent:(pn,params)" ++ (showGhc (pn,params))
  addActualParamsToRhs True pn params t


-- |Do refactoring in the client module. that is to hide the identifer
-- in the import declaration if it will cause any problem in the
-- client module.
liftingInClientMod :: GHC.ModuleName -> [GHC.Name] -> TargetModule
  -> RefactGhc [ApplyRefacResult]
liftingInClientMod serverModName pns targetModule@(_,modSummary) = do
       void $ activateModule targetModule
       renamed <- getRefactRenamed
       -- logm $ "liftingInClientMod:renamed=" ++ (SYB.showData SYB.Renamer 0 renamed) -- ++AZ++
       let clientModule = GHC.ms_mod modSummary
       logm $ "liftingInClientMod:clientModule=" ++ (showGhc clientModule)
  -- = do (inscps, exps ,mod ,ts) <- parseSourceFile fileName
       -- let modNames = willBeUnQualImportedBy serverModName mod
       modNames <- willBeUnQualImportedBy serverModName
       logm $ "liftingInClientMod:modNames=" ++ (showGhc modNames)
       if isJust modNames
        then do
             pns' <- namesNeedToBeHided clientModule (gfromJust "liftingInClientMod" modNames) pns
             logm $ "liftingInClientMod:pns'=" ++ (showGhc pns')
             -- in if pns' /= []
             if (nonEmptyList pns')
                 -- then do <-runStateT (addHiding serverModName mod pns') ((ts,unmodified),(-1000,0))
                 then do (refactoredMod,_) <- applyRefac (addHiding serverModName renamed pns') RSAlreadyLoaded
                         return [refactoredMod]
                 else return []
        else return []

-- |Test whether an identifier defined in the modules specified by
-- 'names' will be exported by current module.
willBeExportedByClientMod :: [GHC.ModuleName] -> GHC.RenamedSource -> Bool
willBeExportedByClientMod names renamed =
  let (_,_,exps,_) = renamed
  in if isNothing exps
        then False
        else any isJust $ map (\y-> (find (\x-> (simpModule x==Just y)) (gfromJust "willBeExportedByClientMod" exps))) names
     where simpModule (GHC.L _ (GHC.IEModuleContents m)) = Just m
           simpModule _  = Nothing

-- |get the module name or alias name by which the lifted identifier
-- will be imported automatically.
-- TODO: maybe move this into TypeUtils
-- willBeUnQualImportedBy::HsName.ModuleName->HsModuleP->Maybe [HsName.ModuleName]
willBeUnQualImportedBy :: GHC.ModuleName -> RefactGhc (Maybe [GHC.ModuleName])
willBeUnQualImportedBy modName = do
   (_,imps,_,_) <- getRefactRenamed
   let ms = filter (\(GHC.L _ (GHC.ImportDecl (GHC.L _ modName1) _qualify _source _safe isQualified _isImplicit _as h))
                     -> modName == modName1 && (not isQualified) && (isNothing h || (isJust h && ((fst (fromJust h)) == True))))
                   imps

       res = if (emptyList ms) then Nothing
                               else Just $ nub $ map getModName ms

       getModName (GHC.L _ (GHC.ImportDecl (GHC.L _ modName2) _qualify _source _safe _isQualified _isImplicit as _h))
        = if isJust as then simpModName (fromJust as)
                       else modName2

       simpModName m = m

   logm $ "willBeUnQualImportedBy:(ms,res)=" ++ (showGhc (ms,res))

   return res


-- |get the subset of 'pns', which need to be hided in the import
-- declaration in module 'mod'
-- Note: these are newly exported from the module, so we cannot use
-- the GHC name resolution i nthis case.
namesNeedToBeHided :: GHC.Module -> [GHC.ModuleName] -> [GHC.Name]
   -> RefactGhc [GHC.Name]
namesNeedToBeHided clientModule modNames pns = do
  renamed <- getRefactRenamed
  parsed <- getRefactParsed
  logm $ "namesNeedToBeHided:willBeExportedByClientMod=" ++ (show $ willBeExportedByClientMod modNames renamed)
  gnames <- GHC.getNamesInScope
  let clientInscopes = filter (\n -> clientModule == GHC.nameModule n) gnames
  logm $ "namesNeedToBeHided:(clientInscopes)=" ++ (showGhc (clientInscopes))

  pnsMapped <- mapM getLocalEquiv pns
  logm $ "namesNeedToBeHided:pnsMapped=" ++ (showGhc pnsMapped)

  let pnsMapped' = filter (\(_,_,ns) -> not $ emptyList ns) pnsMapped

  if willBeExportedByClientMod modNames renamed
      then return pns
      else do
        ff <- mapM (needToBeHided parsed) pnsMapped'
        return $ concat ff
  where
    -- | Strip the package prefix from the name and return the
    -- stripped name together with any names in the local module that
    -- may match the stripped one
    getLocalEquiv :: GHC.Name -> RefactGhc (GHC.Name,String,[GHC.Name])
    getLocalEquiv pn = do
      let pnStr = stripPackage $ showGhc pn
      logm $ "MoveDef getLocalEquiv: about to parseName:" ++ (show pnStr)
      ecns <- GHC.gtry $ GHC.parseName pnStr
      let cns = case ecns of
                 Left (_e::SomeException) -> []
                 Right v -> v
      logm $ "MoveDef getLocalEquiv: cns:" ++ (showGhc cns)
      return (pn,pnStr,cns)

    stripPackage :: String -> String
    stripPackage str = reverse s
      where
        (s,_) = break (== '.') $ reverse str

    needToBeHided :: GHC.ParsedSource -> (GHC.Name,String,[GHC.Name]) -> RefactGhc [GHC.Name]
    needToBeHided parsed (pn,_pnStr,pnsLocal) = do
      let uwoq = map (\n -> usedWithoutQualR n parsed) pnsLocal

      -- logm $ "needToBeHided:(hsBinds renamed)=" ++ (showGhc (hsBinds renamed))
      logm $ "needToBeHided:(pn,uwoq)=" ++ (showGhc (pn,uwoq))

      if (any (== True) uwoq --the same name is used in the module unqualifiedly or
                --is exported unqualifiedly by an Ent decl

            -- was || causeNameClashInExports pn modNames renamed)
            -- TODO: ++AZ++ check if next line needs to be reinstated
            -- was || any (\m -> causeNameClashInExports oldPN pn m renamed) modNames)
            || False)
           then return [pn]
           else return []


-- **************************************************************************************************************--

{- Refactoring Names: 'liftOneLevel'
   Descritption:
    this refactoring lifts a local function/pattern binding only one level up.
    By 'lifting one-level up' ,I mean:

    case1: In a module (HsModule SrcLoc ModuleName (Maybe [HsExportSpecI i]) [HsImportDeclI i] ds):
           A local declaration D  will be lifted to the same level as the 'ds', if D is in the 
           where clause of one of ds's element declaration.

        new: (HsGroup Name, [LImportDecl Name], Maybe [LIE Name], Maybe LHsDocString)
              HsGroup hs_valds :: HsValBinds id ...



    case2: In a match ( HsMatch SrcLoc i [p] (HsRhs e) ds) :
          A local declaration D  will be lifted to the same level as the 'ds', if D is in the 
           where clause of one of ds's element declaration.
           A declaration D,say,in the rhs expression 'e' will be lifted to 'ds' if D is Not local to
           other declaration list in 'e'

           (in a FunBind)
        new: Match [LPat id] (Maybe (LHsType id)) (GRHSs id)


    case3: In a pattern  binding (HsPatBind SrcLoc p (HsRhs e) ds):
           A local declaration D  will be lifted to the same level as the 'ds', if D is in the 
           where clause of one of ds's element declaration.
           A declaration D,say,in the rhs expression 'e' will be lifted to 'ds' if D is Not local to
           other declaration list in 'e'

        new: PatBind (LPat idL) (GRHSs idR) PostTcType NameSet (Maybe tickish)



    case4: In the Let expression (Exp (HsLet ds e):
           A local declaration D  will be lifted to the same level as the 'ds', if D is in the 
           where clause of one of ds's element declaration.
           A declaration D, say, in the expression 'e' will be lifted to 'ds' if D is not local to
           other declaration list in 'e'

        new: HsLet (HsLocalBinds id) (LHsExpr id)


    case5: In the case Alternative expression:(HsAlt loc p rhs ds)
           A local declaration D  will be lifted to the same level as the 'ds', if D is in the 
           where clause of one of ds's element declaration.
           A declaration D in 'rhs' will be lifted to 'ds' if D is not local to other declaration 
           list in 'rhs'.

        new: HsCase (LHsExpr id) (MatchGroup id)
           new is same as in a FunBind.


    case6: In the do statement expression:(HsLetStmt ds stmts)
           A local declaration D  will be lifted to the same level as the 'ds', if D is in the 
           where clause of one of ds's element declaration.
           A declaration D in 'stmts' will be lifted to 'ds' if D is not local to other declaration 
           list in 'stmts'.

        new: LetStmt (HsLocalBindsLR idL idR)
             in context GRHS [LStmt id] (LHsExpr id)


Function name: liftOneLevel
parameters: fileName--current file name.
            mod -- the scoped abstract syntax tree of the module.
            pn  -- the function/pattern name to be lifted.

-}

liftOneLevel' :: GHC.ModuleName
                -> GHC.Located GHC.Name
                -> RefactGhc [ApplyRefacResult]

liftOneLevel' modName pn@(GHC.L _ n) = do
  renamed <- getRefactRenamed
  if isLocalFunOrPatName n renamed
        then do -- (mod', ((toks',m),_))<-liftOneLevel''
                (refactoredMod,_) <- applyRefac (liftOneLevel'') RSAlreadyLoaded
                let (b, pns) = liftedToTopLevel pn renamed
                if b &&  modIsExported modName renamed
                  then do clients<-clientModsAndFiles modName
                          -- logm $ "liftOneLevel':(clients,declPns)=" ++ (showGhc (clients,declPns))
                          refactoredClients <- mapM (liftingInClientMod modName pns) clients
                          return (refactoredMod:(concat refactoredClients))
                  else do return [refactoredMod]
        else error "\nThe identifer is not a function/pattern name!"

   where
      liftOneLevel''= do
             logm $ "in liftOneLevel''"
             renamed <- getRefactRenamed
             ztransformStagedM SYB.Renamer (Nothing
                                `SYB.mkQ` liftToModQ
                                `SYB.extQ` liftToMatchQ'
                                `SYB.extQ` liftToLet'
                                -- `SYB.mkQ` liftToMatchQ
                                -- `SYB.extQ` liftToLet
                                    ) (Z.toZipper renamed)

           where
             isValBinds :: GHC.HsValBinds GHC.Name -> Bool
             isValBinds _ = True

             isGRHSs :: GHC.GRHSs GHC.Name -> Bool
             isGRHSs _ = True

             isHsLet :: GHC.HsExpr GHC.Name -> Bool
             isHsLet (GHC.HsLet _ _) = True
             isHsLet _               = False

             liftToModQ ((g,_imps,_exps,_docs):: GHC.RenamedSource)
                | nonEmptyList candidateBinds
                  = Just (doLiftZ candidateBinds)
                | otherwise = Nothing
                where
                 candidateBinds = map snd
                                $ filter (\(l,_bs) -> nonEmptyList l)
                                $ map (\bs -> (definingDeclsNames [n] (hsBinds bs) False False,bs))
                                $ (hsBinds g)

             liftToMatchQ' :: (SYB.Data a) => GHC.Match GHC.Name -> Maybe (SYB.Stage -> Z.Zipper a -> RefactGhc (Z.Zipper a))
             liftToMatchQ' ((GHC.Match _pats _mtyp (GHC.GRHSs rhs ds))::GHC.Match GHC.Name)
                 | (nonEmptyList (definingDeclsNames [n] (hsBinds  ds) False False))
                    = Just (doLiftZ ds)
                 | (nonEmptyList (definingDeclsNames [n] (hsBinds rhs) False False))
                    = Just (doLiftZ rhs)
                 | otherwise = Nothing

             liftToLet' :: GHC.HsExpr GHC.Name -> Maybe (SYB.Stage -> Z.Zipper a -> RefactGhc (Z.Zipper a))
             liftToLet' ((GHC.HsLet ds _e)::GHC.HsExpr GHC.Name)
               | nonEmptyList (definingDeclsNames [n] (hsBinds ds) False  False)
                 = Just (doLiftZ ds)
               | otherwise = Nothing
             liftToLet' _ = Nothing

             doLiftZ :: (HsValBinds t)
               => t -> SYB.Stage -> Z.Zipper a
               -> RefactGhc (Z.Zipper a)
             doLiftZ ds _stage z =
                  do
                    logm $ "in liftOneLevel''.liftToLet in ds"

                    let zu = case (Z.up z) of
                              Just zz -> fromMaybe (error "MoveDef.liftToLet.1")
                                  $ upUntil (False `SYB.mkQ` isGRHSs
                                                   `SYB.extQ` isHsLet
                                                   `SYB.extQ` isValBinds)
                                     zz
                              Nothing -> z

                    let
                      wtop (ren::GHC.RenamedSource) = do
                        worker ren (hsBinds ds) pn True

                      wgrhs (grhss::GHC.GRHSs GHC.Name) = do
                         (_,dd) <- (hsFreeAndDeclaredPNs grhss)
                         worker1 grhss (hsBinds ds) pn dd False

                      wlet :: GHC.HsExpr GHC.Name -> RefactGhc (GHC.HsExpr GHC.Name)
                      wlet l@(GHC.HsLet dsl _e) = do
                        (_,dd) <- hsFreeAndDeclaredPNs dsl
                        dsl' <- worker1 l (hsBinds ds) pn dd False
                        return dsl'
                      wlet x = return x

                      wvalbinds (vb::GHC.HsValBinds GHC.Name) = do
                         (_,dd) <- (hsFreeAndDeclaredPNs vb)
                         worker1 vb (hsBinds ds) pn dd False

                    ds' <- Z.transM (SYB.mkM wtop `SYB.extM` wgrhs
                                     `SYB.extM` wlet `SYB.extM` wvalbinds) zu

                    return ds'

             -- TODO: merge worker and worker1
             worker :: (HsValBinds t,GHC.Outputable t)
                => t -- ^The destination of the lift operation
                -> [GHC.LHsBind GHC.Name] -- ^ list containing the
                                -- decl to be lifted
                -> GHC.Located GHC.Name -- ^ The name of the decl to
                                -- be lifted
                -> Bool -- ^True if lifting to the top level
                -> RefactGhc t
             worker dest ds pnn toToplevel
                  =do let (before,parent,after)=divideDecls ds pnn -- parent is misnomer, it is the decl to be moved
                          liftedDecls=definingDeclsNames [n] parent True  True
                          declaredPns=nub $ concatMap definedPNs liftedDecls
                      (_, dd) <- hsFreeAndDeclaredPNs dest
                      pns<-pnsNeedRenaming dest parent liftedDecls declaredPns
                      logm $ "MoveDef.worker: pns=" ++ (showGhc pns)
                      if pns==[]
                        then do
                                (parent',liftedDecls',_mLiftedSigs')<-addParamsToParentAndLiftedDecl n dd
                                                                     parent liftedDecls Nothing
                                --True means the new decl will be at the same level with its parant. 
                                dest' <- moveDecl1 (replaceBinds dest (before++parent'++after))
                                           (Just (ghead "worker" (definedPNs (ghead "worker" parent'))))
                                           [n] (Just liftedDecls') declaredPns toToplevel -- False -- ++AZ++ TODO: should be True for toplevel move
                                return dest'
                                --parent'<-doMoving declaredPns (ghead "worker" parent) True  paramAdded parent'
                                --return (before++parent'++liftedDecls''++after)
                        else askRenamingMsg pns "lifting"

             worker1 :: (HsValBinds t,GHC.Outputable t)
                => t -- ^The destination of the lift operation
                -> [GHC.LHsBind GHC.Name] -- ^ list containing the
                                -- decl to be lifted
                -> GHC.Located GHC.Name -- ^ The name of the decl to
                                -- be lifted
                -> [GHC.Name] -- ^Declared variables in the destination
                -> Bool -- ^True if lifting to the top level
                -> RefactGhc t
             worker1 dest ds pnn dd toToplevel
                  {-
                  Actions required
                    1. add parameters to original decls if required
                    2. add parameters to any points that call the lifted decl
                       once it is lifted
                    3. Replace the above in the AST
                    4. Do the move
                  -}

                  =do let (_before,decl,_after)=divideDecls ds pnn
                          liftedDecls=definingDeclsNames [n] decl True  True
                          declaredPns=nub $ concatMap definedPNs liftedDecls

                      pns <- pnsNeedRenaming dest decl liftedDecls declaredPns
                      logm $ "MoveDef.worker1: pns=" ++ (showGhc pns)
                      if pns==[]
                        then do
                                (parent',liftedDecls',_mLiftedSigs')
                                    <- addParamsToParentAndLiftedDecl n dd dest liftedDecls Nothing
                                --True means the new decl will be at the same level with its parant. 
                                parent'' <- moveDecl1 parent' Nothing
                                             [n] (Just liftedDecls') declaredPns toToplevel -- False -- ++AZ++ TODO: should be True for toplevel move
                                return parent''
                                --decl'<-doMoving declaredPns (ghead "worker" decl) True  paramAdded decl'
                                --return (before++decl'++liftedDecls''++after)
                        else askRenamingMsg pns "lifting"


liftedToTopLevel :: GHC.Located GHC.Name -> GHC.RenamedSource -> (Bool,[GHC.Name])
liftedToTopLevel pnt@(GHC.L _ pn) renamed
  = if nonEmptyList (definingDeclsNames [pn] (hsBinds renamed) False True)
     then let (_, parent,_) = divideDecls (hsBinds renamed) pnt
              liftedDecls=definingDeclsNames [pn] (hsBinds parent) True True
              declaredPns  = nub $ concatMap definedPNs liftedDecls
          in (True, declaredPns)
     else (False, [])


addParamsToParentAndLiftedDecl :: (HsValBinds t,GHC.Outputable t) =>
     GHC.Name   -- ^name of decl being lifted
  -> [GHC.Name] -- ^Declared names in parent
  -> t          -- ^parent
  -> [GHC.LHsBind GHC.Name] -- ^decls being lifted
  -> Maybe (GHC.LSig GHC.Name) -- ^ lifted decls signature if present
  -> RefactGhc (t, [GHC.LHsBind GHC.Name], Maybe (GHC.LSig GHC.Name))
addParamsToParentAndLiftedDecl pn dd parent liftedDecls mLiftedSigs
  =do  (ef,_) <- hsFreeAndDeclaredPNs parent
       (lf,_) <- hsFreeAndDeclaredPNs liftedDecls

       -- logm $ "addParamsToParentAndLiftedDecl:parent=" ++ (showGhc parent)

       -- parameters to be added to pn because of lifting
       let newParams= ((nub lf) \\ (nub ef)) \\ dd

       logm $ "addParamsToParentAndLiftedDecl:(newParams,ef,lf,dd)=" ++ (showGhc (newParams,ef,lf,dd))

       if newParams /= []
         then if  (any isComplexPatBind liftedDecls)
                then error "This pattern binding cannot be lifted, as it uses some other local bindings!"
                else do -- first remove the decls to be lifted, so they are not disturbed
                        (parent'',liftedDecls'',_msig) <- rmDecl pn False parent

                        parent' <- addParamsToParent pn newParams parent''

                        liftedDecls' <- addParamsToDecls [liftedDecls''] pn newParams True

                        mLiftedSigs' <- addParamsToSigs newParams mLiftedSigs

                        logm $ "addParamsToParentAndLiftedDecl:mLiftedSigs'=" ++ showGhc mLiftedSigs'

                        return (parent',liftedDecls', mLiftedSigs')
         else return (parent,liftedDecls,mLiftedSigs)

-- ---------------------------------------------------------------------

-- TODO: perhaps move this to TypeUtils
addParamsToSigs :: [GHC.Name] -> Maybe (GHC.LSig GHC.Name) -> RefactGhc (Maybe (GHC.LSig GHC.Name))
addParamsToSigs _ Nothing = return Nothing
addParamsToSigs [] ms = return ms
addParamsToSigs newParams (Just (GHC.L l (GHC.TypeSig lns ltyp@(GHC.L lt _)))) = do
  mts <- mapM getTypeForName newParams
  let ts = catMaybes mts
  -- Note : the '::' symbol lies between the lns and the ltyp. Hence
  --        construct a new location covering this gap, to insert the mew
  --        params. This span has been specifically inserted into the
  --        TokenTree when it is initially loaded.
  let ne = GHC.srcSpanEnd $ GHC.getLoc  $ glast "addParamsToSigs" lns
      ls = GHC.srcSpanStart $ lt
      replaceSpan = GHC.mkSrcSpan ne ls
      newStr = ":: " ++ (intercalate " -> " $ map printSigComponent ts) ++ " -> "
  logm $ "addParamsToSigs:replaceSpan=" ++ showGhc replaceSpan
  logm $ "addParamsToSigs:newStr=[" ++ newStr ++ "]"
  let newToks = basicTokenise newStr
  void $ putToksForSpan replaceSpan newToks
  let typ' = foldl addOneType ltyp ts
  sigOk <- isNewSignatureOk ts
  logm $ "addParamsToSigs:(sigOk,newStr)=" ++ show (sigOk,newStr)
  if sigOk
    then return $ Just (GHC.L l (GHC.TypeSig lns typ'))
    else error $ "\nNew type signature may fail type checking: " ++ newStr ++ "\n"
  where
    addOneType :: GHC.LHsType GHC.Name -> GHC.Type -> GHC.LHsType GHC.Name
    addOneType et t = GHC.noLoc (GHC.HsFunTy (GHC.noLoc hst) et)
      where
        hst = typeToHsType t

addParamsToSigs np ls = error $ "addParamsToSigs: no match for:" ++ showGhc (np,ls)

-- ---------------------------------------------------------------------

printSigComponent :: GHC.Type -> String
printSigComponent x = ppType x

-- ---------------------------------------------------------------------

-- |Fail any signature having a forall in it.
-- TODO: this is unnecesarily restrictive, but needs
-- a) proper reversing of GHC.Type to GHC.LhsType
-- b) some serious reverse type inference to ensure that the
--    constraints are modified properly to merge the old signature
--    part and the new.
isNewSignatureOk :: [GHC.Type] -> RefactGhc Bool
isNewSignatureOk types = do
  -- NOTE: under some circumstances enabling Rank2Types or RankNTypes
  --       can resolve the type conflict, this can potentially be checked
  --       for.
  -- NOTE2: perhaps proceed and reload the tentative refactoring into
  --        the GHC session and accept it only if it type checks
  let
    r = SYB.everythingStaged SYB.TypeChecker (++) []
          ([] `SYB.mkQ` usesForAll) types
    usesForAll (GHC.ForAllTy _ _) = [1::Int]
    usesForAll _                  = []

  -- logm $ "isNewSignatureOk:r=" ++ show r
  return $ emptyList r

-- ---------------------------------------------------------------------

-- TODO: perhaps move this to TypeUtils
-- TODO: complete this
typeToHsType :: GHC.Type -> GHC.HsType GHC.Name
typeToHsType (GHC.TyVarTy v) = GHC.HsTyVar (Var.varName v)
typeToHsType (GHC.AppTy t1 t2) = GHC.HsAppTy (GHC.noLoc $ typeToHsType t1)
                                             (GHC.noLoc $ typeToHsType t2)

typeToHsType t@(GHC.TyConApp _tc _ts) = tyConAppToHsType t

typeToHsType (GHC.FunTy t1 t2) = GHC.HsFunTy (GHC.noLoc $ typeToHsType t1)
                                             (GHC.noLoc $ typeToHsType t2)
#if __GLASGOW_HASKELL__ > 704
typeToHsType (GHC.ForAllTy _v t) = GHC.HsForAllTy GHC.Explicit (GHC.HsQTvs [] []) (GHC.noLoc []) (GHC.noLoc $ typeToHsType t)
#else
typeToHsType (GHC.ForAllTy _v t) = GHC.HsForAllTy GHC.Explicit [] (GHC.noLoc []) (GHC.noLoc $ typeToHsType t)
#endif

#if __GLASGOW_HASKELL__ > 704
typeToHsType (GHC.LitTy (GHC.NumTyLit i)) = GHC.HsTyLit (GHC.HsNumTy i)
typeToHsType (GHC.LitTy (GHC.StrTyLit s)) = GHC.HsTyLit (GHC.HsStrTy s)
#endif

{-
data Type
  = TyVarTy Var	-- ^ Vanilla type or kind variable (*never* a coercion variable)

  | AppTy         -- See Note [AppTy invariant]
	Type
	Type		-- ^ Type application to something other than a 'TyCon'. Parameters:
	                --
                        --  1) Function: must /not/ be a 'TyConApp',
                        --     must be another 'AppTy', or 'TyVarTy'
	                --
	                --  2) Argument type

  | TyConApp      -- See Note [AppTy invariant]
	TyCon
	[KindOrType]	-- ^ Application of a 'TyCon', including newtypes /and/ synonyms.
	                -- Invariant: saturated appliations of 'FunTyCon' must
	                -- use 'FunTy' and saturated synonyms must use their own
                        -- constructors. However, /unsaturated/ 'FunTyCon's
                        -- do appear as 'TyConApp's.
	                -- Parameters:
	                --
	                -- 1) Type constructor being applied to.
	                --
                        -- 2) Type arguments. Might not have enough type arguments
                        --    here to saturate the constructor.
                        --    Even type synonyms are not necessarily saturated;
                        --    for example unsaturated type synonyms
	                --    can appear as the right hand side of a type synonym.

  | FunTy
	Type
	Type		-- ^ Special case of 'TyConApp': @TyConApp FunTyCon [t1, t2]@
			-- See Note [Equality-constrained types]

  | ForAllTy
	Var         -- Type or kind variable
	Type	        -- ^ A polymorphic type

  | LitTy TyLit     -- ^ Type literals are simillar to type constructors.

-}

tyConAppToHsType :: GHC.Type -> GHC.HsType GHC.Name
tyConAppToHsType (GHC.TyConApp tc _ts)
  | GHC.isFunTyCon tc = r "isFunTyCon"
  | GHC.isAlgTyCon tc = r "isAlgTyCon"
  | GHC.isTupleTyCon tc = r "isTupleTyCon"
  | GHC.isSynTyCon tc = r "isSynTyCon"
  | GHC.isPrimTyCon tc = r "isPrimTyCon"
#if __GLASGOW_HASKELL__ > 704
  | GHC.isPromotedDataCon tc = r "isPromotedDataTyCon"
  | GHC.isPromotedTyCon tc =  r "isPromotedTyCon"
#endif
  where

#if __GLASGOW_HASKELL__ > 704
    r str = GHC.HsTyLit (GHC.HsStrTy $ GHC.mkFastString str)
#else
    r str = error $ "tyConAppToHsType: " ++ str ++ " unexpected:" ++ (SYB.showData SYB.TypeChecker 0 r)
#endif

tyConAppToHsType t@(GHC.TyConApp _tc _ts)
   = error $ "tyConAppToHsType: unexpected:" ++ (SYB.showData SYB.TypeChecker 0 t)

{-
HsType
HsForAllTy HsExplicitFlag (LHsTyVarBndrs name) (LHsContext name) (LHsType name)
HsTyVar name
HsAppTy (LHsType name) (LHsType name)
HsFunTy (LHsType name) (LHsType name)
HsListTy (LHsType name)
HsPArrTy (LHsType name)
HsTupleTy HsTupleSort [LHsType name]
HsOpTy (LHsType name) (LHsTyOp name) (LHsType name)
HsParTy (LHsType name)
HsIParamTy HsIPName (LHsType name)
HsEqTy (LHsType name) (LHsType name)
HsKindSig (LHsType name) (LHsKind name)
HsQuasiQuoteTy (HsQuasiQuote name)
HsSpliceTy (HsSplice name) FreeVars PostTcKind
HsDocTy (LHsType name) LHsDocString
HsBangTy HsBang (LHsType name)
HsRecTy [ConDeclField name]
HsCoreTy Type
HsExplicitListTy PostTcKind [LHsType name]
HsExplicitTupleTy [PostTcKind] [LHsType name]
HsTyLit HsTyLit
HsWrapTy HsTyWrapper (HsType name)
-}




{-
  = -- | The function type constructor, @(->)@
    FunTyCon {
        tyConUnique :: Unique,
        tyConName   :: Name,
        tc_kind   :: Kind,
        tyConArity  :: Arity
    }

  -- | Algebraic type constructors, which are defined to be those
  -- arising @data@ type and @newtype@ declarations.  All these
  -- constructors are lifted and boxed. See 'AlgTyConRhs' for more
  -- information.
  | AlgTyCon {
        tyConUnique :: Unique,
        tyConName   :: Name,
        tc_kind     :: Kind,
        tyConArity  :: Arity,

        tyConTyVars :: [TyVar],   -- ^ The kind and type variables used in the type constructor.
                                  -- Invariant: length tyvars = arity
                                  -- Precisely, this list scopes over:
                                  --
                                  -- 1. The 'algTcStupidTheta'
                                  -- 2. The cached types in 'algTyConRhs.NewTyCon'
                                  -- 3. The family instance types if present
                                  --
                                  -- Note that it does /not/ scope over the data constructors.
        tyConCType   :: Maybe CType, -- The C type that should be used
                                     -- for this type when using the FFI
                                     -- and CAPI

        algTcGadtSyntax  :: Bool,       -- ^ Was the data type declared with GADT syntax?
                                        -- If so, that doesn't mean it's a true GADT;
                                        -- only that the "where" form was used.
                                        -- This field is used only to guide pretty-printing

        algTcStupidTheta :: [PredType], -- ^ The \"stupid theta\" for the data type
                                        -- (always empty for GADTs).
                                        -- A \"stupid theta\" is the context to the left
                                        -- of an algebraic type declaration,
                                        -- e.g. @Eq a@ in the declaration
                                        --    @data Eq a => T a ...@.

        algTcRhs :: AlgTyConRhs,  -- ^ Contains information about the
                                  -- data constructors of the algebraic type

        algTcRec :: RecFlag,      -- ^ Tells us whether the data type is part
                                  -- of a mutually-recursive group or not

        algTcParent :: TyConParent      -- ^ Gives the class or family declaration 'TyCon'
                                        -- for derived 'TyCon's representing class
                                        -- or family instances, respectively.
                                        -- See also 'synTcParent'
    }

  -- | Represents the infinite family of tuple type constructors,
  --   @()@, @(a,b)@, @(# a, b #)@ etc.
  | TupleTyCon {
        tyConUnique    :: Unique,
        tyConName      :: Name,
        tc_kind        :: Kind,
        tyConArity     :: Arity,
        tyConTupleSort :: TupleSort,
        tyConTyVars    :: [TyVar],
        dataCon        :: DataCon -- ^ Corresponding tuple data constructor
    }

  -- | Represents type synonyms
  | SynTyCon {
        tyConUnique  :: Unique,
        tyConName    :: Name,
        tc_kind    :: Kind,
        tyConArity   :: Arity,

        tyConTyVars  :: [TyVar],        -- Bound tyvars

        synTcRhs     :: SynTyConRhs,    -- ^ Contains information about the
                                        -- expansion of the synonym

        synTcParent  :: TyConParent     -- ^ Gives the family declaration 'TyCon'
                                        -- of 'TyCon's representing family instances

    }

  -- | Primitive types; cannot be defined in Haskell. This includes
  -- the usual suspects (such as @Int#@) as well as foreign-imported
  -- types and kinds
  | PrimTyCon {
        tyConUnique   :: Unique,
        tyConName     :: Name,
        tc_kind       :: Kind,
        tyConArity    :: Arity,         -- SLPJ Oct06: I'm not sure what the significance
                                        --             of the arity of a primtycon is!

        primTyConRep  :: PrimRep,       -- ^ Many primitive tycons are unboxed, but some are
                                        --   boxed (represented by pointers). This 'PrimRep'
                                        --   holds that information.
                                        -- Only relevant if tc_kind = *

        isUnLifted   :: Bool,           -- ^ Most primitive tycons are unlifted
                                        --   (may not contain bottom)
                                        --   but foreign-imported ones may be lifted

        tyConExtName :: Maybe FastString   -- ^ @Just e@ for foreign-imported types,
                                           --   holds the name of the imported thing
    }

  -- | Represents promoted data constructor.
  | PromotedDataCon {         -- See Note [Promoted data constructors]
        tyConUnique :: Unique, -- ^ Same Unique as the data constructor
        tyConName   :: Name,   -- ^ Same Name as the data constructor
        tyConArity  :: Arity,
        tc_kind     :: Kind,   -- ^ Translated type of the data constructor
        dataCon     :: DataCon -- ^ Corresponding data constructor
    }

  -- | Represents promoted type constructor.
  | PromotedTyCon {
        tyConUnique :: Unique, -- ^ Same Unique as the type constructor
        tyConName   :: Name,   -- ^ Same Name as the type constructor
        tyConArity  :: Arity,  -- ^ n if ty_con :: * -> ... -> *  n times
        tc_kind     :: Kind,   -- ^ Always TysPrim.superKind
        ty_con      :: TyCon   -- ^ Corresponding type constructor
    }

  deriving Typeable

-}

--------------------------------End of Lifting-----------------------------------------

{-Refactoring : demote a function/pattern binding(simpe or complex) to the declaration where it is used.
  Descritption: if a declaration D, say, is only used by another declaration F,say, then D can be 
                demoted into the local declaration list (where clause) in F.
                So currently, D can not be demoted if more than one declaration use it. 

                In a multi-module context, a top-level definition can not be demoted if it is used
                by other modules. In the case that the demoted identifer is in the hiding list of
                import declaration in a client module, it should be removed from the hiding list.

 Function name:demote
 parameters: fileName--current file name.
             mod -- the scoped abstract syntax tree of the module.
             pn  -- the function/pattern name to be demoted.

-}

demote' ::
     GHC.ModuleName
  -- -> FilePath
  -- -> (ParseResult,[PosToken])
  -> GHC.Located GHC.Name
  -> RefactGhc [ApplyRefacResult]
demote' modName (GHC.L _ pn) = do
  renamed <- getRefactRenamed
  if isFunOrPatName pn renamed
    then do
       isTl <- isTopLevelPN pn
       if isTl && isExplicitlyExported pn renamed
          then error "This definition can not be demoted, as it is explicitly exported by the current module!"
          else do -- (mod',((toks',m),_))<-doDemoting pn fileName mod toks
                  (refactoredMod,_) <- applyRefac (doDemoting pn) RSAlreadyLoaded
                  -- isTl <- isTopLevelPN pn
                  if isTl && modIsExported modName renamed
                    then do let demotedDecls'= definingDeclsNames [pn] (hsBinds renamed) True False
                                declaredPns  = nub $ concatMap definedPNs demotedDecls'
                            clients <- clientModsAndFiles modName
                            logm $ "demote':clients=" ++ (showGhc clients)
                            refactoredClients <-mapM (demotingInClientMod declaredPns) clients
                            -- return (refactoredMod:[])
                            return (refactoredMod:refactoredClients)
                    else do return [refactoredMod]
    else error "\nInvalid cursor position!"


-- |Do refactoring in the client module, that is:
--  a) Check whether the identifier is used in the module body
--  b) If the identifier is not used but is hided by the import
--     declaration, then remove it from the hiding.
demotingInClientMod ::
  [GHC.Name] -> TargetModule
  -> RefactGhc ApplyRefacResult
demotingInClientMod pns targetModule@(_,modSummary) = do
  void $ activateModule targetModule
  (refactoredMod,_) <- applyRefac (doDemotingInClientMod pns (GHC.ms_mod modSummary)) RSAlreadyLoaded
  return refactoredMod


doDemotingInClientMod :: [GHC.Name] -> GHC.Module -> RefactGhc ()
doDemotingInClientMod pns modName = do
  renamed@(_g,imps,exps,_docs) <- getRefactRenamed
  if any (\pn->findPN pn (hsBinds renamed) || findPN pn (exps)) pns
     then error $ "This definition can not be demoted, as it is used in the client module '"++(showGhc modName)++"'!"
     else if any (\pn->findPN pn imps) pns
             -- TODO: reinstate this
             then do -- (mod',((ts',m),_))<-runStateT (rmItemsFromImport mod pns) ((ts,unmodified),(-1000,0))
                     return ()
             else return ()

doDemoting :: GHC.Name -> RefactGhc ()
doDemoting  pn = do

  clearRefactDone -- Only do this action once

  renamed  <- getRefactRenamed
  -- logm $ "MoveDef.doDemoting:renamed=" ++ (SYB.showData SYB.Renamer 0 renamed) -- ++AZ++

  -- everywhereMStaged' is top-down, does all
  renamed' <- everywhereMStaged' SYB.Renamer (SYB.mkM   demoteInMod
                                             `SYB.extM` demoteInMatch
                                             `SYB.extM` demoteInPat
                                             `SYB.extM` demoteInLet
                                             `SYB.extM` demoteInStmt
                                            ) renamed
  -- error ("doDemoting:renamed'=" ++ (showGhc renamed'))
  putRefactRenamed renamed'
  -- ren <- getRefactRenamed
  -- error ("doDemoting:ren=" ++ (showGhc ren))
  showLinesDebug "doDemoting done"
  return ()
    where
       --1. demote from top level
       -- demoteInMod (mod@(HsModule loc name exps imps ds):: HsModuleP)
       demoteInMod (renamed :: GHC.RenamedSource)
         | not $ emptyList decls
         = do
              logm "MoveDef:demoteInMod" -- ++AZ++
              demoted <- doDemoting' renamed pn
              return demoted
         where
           decls = (definingDeclsNames [pn] (hsBinds renamed) False False)
       demoteInMod x = return x

       --2. The demoted definition is a local decl in a match
       -- demoteInMatch (match@(HsMatch loc1 name pats rhs ds)::HsMatchP)
       demoteInMatch (match@(GHC.Match _pats _mt (GHC.GRHSs _ ds))::GHC.Match GHC.Name)
         -- was | definingDecls [pn] ds False False/=[]
         | not $ emptyList (definingDeclsNames [pn] (hsBinds ds) False False)
         = do
              logm "MoveDef:demoteInMatch" -- ++AZ++
              done <- getRefactDone
              match' <- if (not done)
                then doDemoting' match pn
                else return match
              return match'
       demoteInMatch  x = return x

       --3. The demoted definition is a local decl in a pattern binding
       -- demoteInPat (pat@(Dec (HsPatBind loc p rhs ds))::HsDeclP)
       demoteInPat (pat@((GHC.PatBind _p rhs _ _ _))::GHC.HsBind GHC.Name)
         -- was | definingDecls [pn] ds False False /=[]
         | not $ emptyList (definingDeclsNames [pn] (hsBinds rhs) False False)
          = do
              logm "MoveDef:demoteInPat" -- ++AZ++
              done <- getRefactDone
              pat' <- if (not done)
                then doDemoting' pat pn
                else return pat
              return pat'
       demoteInPat x = return x

       --4: The demoted definition is a local decl in a Let expression
       -- demoteInLet (letExp@(Exp (HsLet ds e))::HsExpP)
       demoteInLet (letExp@(GHC.L _ (GHC.HsLet ds _e))::GHC.LHsExpr GHC.Name)
         -- was | definingDecls [pn] ds False False/=[]
         | not $ emptyList (definingDeclsNames [pn] (hsBinds ds) False False)
          = do
              logm "MoveDef:demoteInLet" -- ++AZ++
              done <- getRefactDone
              letExp' <- if (not done)
                 then doDemoting' letExp pn
                 else return letExp
              return letExp'
       demoteInLet x = return x

       -- TODO: the rest of these cases below
{-
       --5. The demoted definition is a local decl in a case alternative.
       demoteInAlt (alt@(HsAlt loc p rhs ds)::(HsAlt (HsExpP) (HsPatP) [HsDeclP]))
         | definingDecls [pn] ds False False /=[]
          = doDemoting'  alt pn
       demoteInAlt _=mzero
-}

       --6.The demoted definition is a local decl in a Let statement.
       -- demoteInStmt (letStmt@(HsLetStmt ds stmts):: (HsStmt (HsExpP) (HsPatP) [HsDeclP]))
       demoteInStmt (letStmt@(GHC.LetStmt binds)::GHC.Stmt GHC.Name)
         -- was | definingDecls [pn] ds False False /=[]
         | not $ emptyList (definingDeclsNames [pn] (hsBinds binds) False False)
          = do
              logm "MoveDef:demoteInStmt" -- ++AZ++
              done <- getRefactDone
              letStmt' <- if (not done)
                then doDemoting' letStmt pn
                else return letStmt
              return letStmt'
       demoteInStmt x =return x

       -- TODO: the rest of these cases below
{-
       failure=idTP `adhocTP` mod
             where
               mod (m::HsModuleP)
                = error "Refactoring failed!"   --SHOULD GIVE MORE DETAILED ERROR MESSAGE
-}



-- |Demote the declaration of 'pn' in the context of 't'.
doDemoting' :: (HsValBinds t, UsedByRhs t) => t -> GHC.Name -> RefactGhc t
doDemoting' t pn = do
   let origDecls = hsBinds t
       demotedDecls'= definingDeclsNames [pn] origDecls True False
       declaredPns = nub $ concatMap definedPNs demotedDecls'
       pnsUsed = usedByRhs t declaredPns
   logm $ "doDemoting':(pn,declaredPns)=" ++ showGhc (pn,declaredPns)
   -- logm $ "doDemoting':t=" ++ (SYB.showData SYB.Renamer 0 t)
   logm $ "doDemoting':(declaredPns,pnsUsed)=" ++ showGhc (declaredPns,pnsUsed)
   r <-  if not pnsUsed -- (usedByRhs t declaredPns)
       then do
              -- drawTokenTree "" -- ++AZ++ debug
              let demotedDecls = definingDeclsNames [pn] (hsBinds t) True True
              let
                  otherBinds = (deleteFirstsBy sameBind (hsBinds t) demotedDecls)
                  -- uselist = uses declaredPns otherBinds
                      {- From 'hsDecls t' to 'hsDecls t \\ demotedDecls'.
                         Bug fixed 06/09/2004 to handle direct recursive function.
                       -}
                  -- uselist = concatMap (\r -> if (emptyList r) then [] else ["Used"]) $ map (\b -> uses declaredPns [b]) otherBinds
                  xx = map (\b -> (b,uses declaredPns [b])) otherBinds
                  useCount = sum $ concatMap snd xx
              -- logm $ "doDemoting': uses xx=" ++ (showGhc xx)
              -- logm $ "doDemoting': uses useCount=" ++ (show useCount)

              case useCount  of
                  0 ->do error "\n Nowhere to demote this function!\n"
                  1 -> --This function is only used by one friend function
                      do
                         logm "MoveDef.doDemoting':target location found" -- ++AZ++

                         (f,_d) <- hsFreeAndDeclaredPNs demotedDecls
                         (ds,removedDecl,_sigRemoved) <- rmDecl pn False t

                         (t',demotedSigs) <- rmTypeSigs declaredPns ds

                         let (GHC.L ssd _) = removedDecl
                         demotedToks <- getToksForSpan ssd

                         -- TODO: move this to its own fn
                         let getToksForMaybeSig (GHC.L ss _) = do
                                                   sigToks <- getToksForSpan ss
                                                   return sigToks

                         demotedSigToksLists <- mapM getToksForMaybeSig demotedSigs
                         let demotedSigToks = concat demotedSigToksLists
                         -- end TODO

                         logm $ "MoveDef:declaredPns=" ++ (showGhc declaredPns) -- ++AZ++

                         --get those variables declared at where the demotedDecls will be demoted to
                         -- let dl = map (flip declaredNamesInTargetPlace ds) declaredPns
                         dl <- mapM (flip declaredNamesInTargetPlace ds) declaredPns
                         logm $ "mapM declaredNamesInTargetPlace done"
                         --make sure free variable in 'f' do not clash with variables in 'dl',
                         --otherwise do renaming.
                         let clashedNames=filter (\x-> elem (id x) (map id f)) $ (nub.concat) dl
                         --rename clashed names to new names created automatically,update TOKEN STREAM as well.
                         if clashedNames/=[]
                            then error ("The identifier(s):" ++ showGhc clashedNames ++
                                       ", declared in where the definition will be demoted to, will cause name clash/capture"
                                       ++" after demoting, please do renaming first!")
                                 --ds'<-foldM (flip (autoRenameLocalVar True)) ds clashedNames
                            else  --duplicate demoted declarations to the right place.
                                 do
                                    logm $ "MoveDef: about to duplicateDecls"
                                    ds'' <- duplicateDecls declaredPns removedDecl demotedSigs (Just (demotedSigToks ++ demotedToks)) (hsBinds ds)
                                    logm $ "MoveDef:duplicateDecls done"

                                    return (replaceBinds t' ds'')
                  _ ->error "\nThis function/pattern binding is used by more than one friend bindings\n"

       else error "This function can not be demoted as it is used in current level!\n"

   return r

    where
          ---find how many matches/pattern bindings use  'pn'-------
          -- uses :: [GHC.Name] -> [GHC.LHsBind GHC.Name] -> [Int]
          uses pns t2
               = concatMap used t2
                where

                  used :: GHC.LHsBind GHC.Name -> [Int]
                  used (GHC.L _ (GHC.FunBind _n _ (GHC.MatchGroup matches _) _ _ _))
                     = concatMap (usedInMatch pns) matches

                  used (GHC.L _ (GHC.PatBind pat rhs _ _ _))
                    -- was | hsPNs p `intersect` pns ==[]  && any  (flip findPN pat) pns
                    | (not $ findPNs pns pat) && findPNs pns rhs
                    = [1::Int]
                  used  _ = []

          usedInMatch pns (GHC.L _ (GHC.Match pats _ rhs))
            -- was | isNothing (find (==pname) pns) && any  (flip findPN match) pns
            | (not $ findPNs pns pats) && findPNs pns rhs
             = [1::Int]
          usedInMatch _ _ = []


          -- duplicate demotedDecls to the right place (the outer most level where it is used).
          duplicateDecls :: [GHC.Name] -- ^ function names to be demoted
                         -> GHC.LHsBind GHC.Name -- ^Bind being demoted
                         -> [GHC.LSig GHC.Name] -- ^Signatures being demoted, if any
                         -> Maybe [PosToken]          -- ^Tokens if provided
                         -> [GHC.LHsBind GHC.Name]    -- ^Binds of original top level entiity, including src and dst
                         -> RefactGhc [GHC.LHsBind GHC.Name]
          duplicateDecls pns demoted dsig dtoks decls
             -- = do everywhereMStaged SYB.Renamer (SYB.mkM dupInMatch
             = do
                  -- logm "duplicateDecls:clearing done"  -- ++AZ++
                  -- clearRefactDone
                  everywhereMStaged' SYB.Renamer (SYB.mkM dupInMatch -- top-down approach
             -- = do somewhereMStaged SYB.Renamer (SYB.mkM dupInMatch -- need working MonadPlus for somewhereMStaged
                                                `SYB.extM` dupInPat) decls
             {-
             = do applyTP (once_tdTP (failTP `adhocTP` dupInMatch
                                             `adhocTP` dupInPat)) decls
                  --error (show decls' ++ "\n" ++ prettyprint decls')
                  -- rmDecl (ghead "moveDecl3"  pns) False =<<foldM (flip rmTypeSig) decls' pns 
             -}
               where
                 -- dupInMatch (match@(HsMatch loc1 name pats rhs ds)::HsMatchP)
                 dupInMatch (match@(GHC.Match pats _mt rhs) :: GHC.Match GHC.Name)
                   -- was | any (flip findPN match) pns && not (any (flip findPN name) pns)
                   | (not $ findPNs pns pats) && findPNs pns rhs
                   =  do
                        done <- getRefactDone
                        logm $ "duplicateDecls.dupInMatch:value of done=" ++ (show done) -- ++AZ++
                        if done
                          then return match
                          else do
                            logm "duplicateDecls:setting done"  -- ++AZ++
                            setRefactDone
                            --If not fold parameters.
                            -- moveDecl pns pats False decls False
                            {- ++AZ++ foldParams instead
                            rhs' <- addDecl rhs Nothing (demoted,dsig,dtoks) False
                            return (GHC.Match pats mt rhs')
                            -}
                            -- If fold parameters.
                            -- error "dupInMatch" -- ++AZ++
                            match' <- foldParams pns match decls demoted dsig dtoks
                            return match'
                 -- dupInMatch _ =mzero
                 dupInMatch x = return x

                 -- dupInPat (pat@(Dec (HsPatBind loc p rhs ds))::HsDeclP)
                 dupInPat ((GHC.PatBind pat rhs ty fvs ticks) :: GHC.HsBind GHC.Name)
                    -- was |any (flip findPN pat) pns && not (any (flip findPN p) pns)
                    | (not $ findPNs pns pat) && findPNs pns rhs
                   -- =  moveDecl pns pat False decls False
                   = do
                       logm $ "duplicateDecls.dupInPat"
                       -- rhs' <- moveDecl pns rhs False decls False
                       -- TODO: what wbout dtoks?
                       -- error "dupInPat" -- ++AZ++
                       rhs' <- moveDecl1 rhs Nothing pns Nothing pns False
                       return (GHC.PatBind pat rhs' ty fvs ticks)
                 -- dupInPat _ =mzero
                 dupInPat x = return x

                 -- demotedDecls = definingDecls pns decls True False
          ---------------------------------------------------------------------
          {-
          declaredNamesInTargetPlace :: (Term t, MonadPlus m)=>PName->t->m [PName]
          declaredNamesInTargetPlace pn=applyTU (stop_tdTU (failTU
                                                    `adhocTU` inMatch
                                                    `adhocTU` inPat))
          -}
          declaredNamesInTargetPlace :: (SYB.Data t)
                            => GHC.Name -> t
                            -- -> RefactGhc [GHC.Name]
                            -> RefactGhc [GHC.Name]

          declaredNamesInTargetPlace pn' t' = do
             logm $ "declaredNamesInTargetPlace:pn=" ++ (showGhc pn')
             res <- applyTU (stop_tdTUGhc (failTU
                                           `adhocTU` inMatch
                                           `adhocTU` inPat)) t'
             logm $ "declaredNamesInTargetPlace:res=" ++ (showGhc res)
             return res
               where
                 -- inMatch (match@(HsMatch loc1 name pats rhs ds)::HsMatchP)
                 inMatch ((GHC.Match _pats _ rhs) :: GHC.Match GHC.Name)
                    | findPN pn' rhs = do
                     logm $ "declaredNamesInTargetPlace:inMatch"
                     fds <- hsFDsFromInside rhs
                     return $ snd fds
                     -- (return.snd) =<< hsFDsFromInside rhs
                 -- inMatch _ = mzero
                 inMatch _ = return mzero

                 -- inPat (pat@(Dec (HsPatBind loc p rhs ds)):: HsDeclP)
                 inPat ((GHC.PatBind pat rhs _ _ _) :: GHC.HsBind GHC.Name)
                    |findPN pn' rhs = do
                     logm $ "declaredNamesInTargetPlace:inPat"
                     fds <- hsFDsFromInside pat
                     return $ snd fds
                     -- (return.snd) =<< hsFDsFromInside pat
                 -- inPat _=  mzero
                 inPat _=  return mzero



-- ---------------------------------------------------------------------




{- foldParams:remove parameters in the demotedDecls if possible
   parameters: pn -- the function/pattern name to be demoted in PName format
               match--where the demotedDecls will be demoted to
               demotedDecls -- the declarations to be demoted.
   example:
    module Test where        demote 'sq'       module Test where
    sumSquares x y               ===>          sumSquares x y =(sq 0) + (sq y)
      = sq x 0+ sq x y                               where sq y=x ^ y
    sq x y=x^y
-}
--PROBLEM: TYPE SIGNATURE SHOULD BE CHANGED.
--- TEST THIS FUNCTION!!!
foldParams :: [GHC.Name]             -- ^The (list?) function name being demoted
           -> GHC.Match GHC.Name     -- ^The RHS of the place to receive the demoted decls
           -> [GHC.LHsBind GHC.Name] -- ^Binds of original top level entiity, including src and dst
           -> GHC.LHsBind GHC.Name   -- ^The decls being demoted
           -> [GHC.LSig GHC.Name]    -- ^Signatures being demoted, if any
           -> Maybe [PosToken]          -- ^Tokens if provided
           -> RefactGhc (GHC.Match GHC.Name)
foldParams pns ((GHC.Match pats mt rhs)::GHC.Match GHC.Name) _decls demotedDecls dsig dtoks

     =do
         logm $ "MoveDef.foldParams entered"
         -- logm $ "MoveDef.foldParams:match=" ++ (SYB.showData SYB.Renamer 0 match)

         let matches=concatMap matchesInDecls [GHC.unLoc demotedDecls]
             pn=ghead "foldParams" pns    --pns /=[]
         params <- allParams pn rhs []
         if (length.nub.map length) params==1                  -- have same number of param 
             && ((length matches)==1)      -- only one 'match' in the demoted declaration
           then do
                   let patsInDemotedDecls=(patsInMatch.(ghead "foldParams")) matches
                       subst=mkSubst patsInDemotedDecls params
                       fstSubst=map fst subst
                       sndSubst=map snd subst

                   -- logm $ "MoveDef.foldParams before rmParamsInParent"
                   rhs' <- rmParamsInParent pn sndSubst rhs
                   -- logm $ "MoveDef.foldParams after rmParamsInParent"

                   -- ls<-mapM hsFreeAndDeclaredPNs sndSubst
                   -- ls <- mapM hsFreeAndDeclaredPNs sndSubst
                   ls <- mapM hsFreeAndDeclaredPNs sndSubst
                   -- newNames contains the newly introduced names to the demoted decls---
                   -- let newNames=(map pNtoName (concatMap fst ls)) \\ (map pNtoName fstSubst)
                   let newNames=((concatMap fst ls)) \\ (fstSubst)
                   --There may be name clashing because of introducing new names.
                   clashedNames<-getClashedNames fstSubst newNames (ghead "foldParams" matches)

                   logm $ "MoveDef.foldParams about to foldInDemotedDecls"

                   -- decls' <- foldInDemotedDecls pns clashedNames subst decls
                   -- let demotedDecls''' = definingDeclsNames pns decls' True False
                   demotedDecls''' <- foldInDemotedDecls pns clashedNames subst [demotedDecls]
                   logm $ "MoveDef.foldParams foldInDemotedDecls done"

                   let [(GHC.L declSpan _)] = demotedDecls'''
                   declToks <- getToksForSpan declSpan
                   -- logm $ "MoveDef.foldParams addDecl adding to (hsBinds):[" ++ (SYB.showData SYB.Renamer 0 $ hsBinds rhs') ++ "]" -- ++AZ++
                   rhs'' <- addDecl rhs' Nothing (ghead "foldParams 2" demotedDecls''',[],Just declToks) False
                   logm $ "MoveDef.foldParams addDecl done 1"
                   return (GHC.Match pats mt rhs'')
           else  do  -- moveDecl pns match False decls True
                     -- return (HsMatch loc1 name pats rhs (ds++demotedDecls))  -- no parameter folding 
                     -- logm $ "MoveDef.foldParams about to addDecl:dtoks=" ++ (show dtoks)
                     -- drawTokenTree "" -- ++AZ++ debug
                     rhs' <- addDecl rhs Nothing (demotedDecls,dsig,dtoks) False
                     logm $ "MoveDef.foldParams addDecl done 2"
                     return (GHC.Match pats mt rhs')

         -- return match
    where

       -- matchesInDecls ((Dec (HsFunBind loc matches))::HsDeclP)=matches
       matchesInDecls (GHC.FunBind _ _ (GHC.MatchGroup matches _) _ _ _) = matches
       matchesInDecls _x = []

       -- patsInMatch ((HsMatch loc1 name pats rhs ds)::HsMatchP)
       --   =pats
       patsInMatch (GHC.L _ (GHC.Match pats' _ _)) = pats'

       -- demotedDecls = map GHC.unLoc $ definingDeclsNames pns decls True False


       foldInDemotedDecls :: [GHC.Name]  -- ^The (list?) of names to be demoted
                          -> [GHC.Name]  -- ^Any names that clash
                          -> [(GHC.Name, GHC.HsExpr GHC.Name)] -- ^Parameter substitutions required
                          -> [GHC.LHsBind GHC.Name] -- ^Binds of original top level entiity, including src and dst
                          -> RefactGhc [GHC.LHsBind GHC.Name]
       foldInDemotedDecls  pns' clashedNames subst decls
          = everywhereMStaged SYB.Renamer (SYB.mkM worker) decls
          where
          -- worker (match@(HsMatch loc1 (PNT pname _ _) pats rhs ds)::HsMatchP)
          worker (match@(GHC.FunBind (GHC.L _ pname) _ (GHC.MatchGroup _matches _) _ _ _) :: GHC.HsBind GHC.Name)
            | isJust (find (==pname) pns')
            = do
                 match'  <- foldM (flip (autoRenameLocalVar True)) match clashedNames
                 match'' <- foldM replaceExpWithUpdToks match' subst
                 rmParamsInDemotedDecls (map fst subst) match''

          worker x = return x

      ------Get all of the paramaters supplied to pn ---------------------------
            {- eg. sumSquares x1 y1 x2 y2 = rt x1 y1 + rt x2 y2
                   rt x y = x+y
              demote 'rt' to 'sumSquares',
              'allParams pn rhs []'  returns [[x1,x2],[y1,y2]]
                where pn is 'rt' and  rhs is 'rt x1 y1 + rt x2 y2'
           -}

       allParams :: GHC.Name -> GHC.GRHSs GHC.Name -> [[GHC.HsExpr GHC.Name]]
                 -> RefactGhc [[GHC.HsExpr GHC.Name]]
       allParams pn rhs1 initial  -- pn: demoted function/pattern name.
        =do -- p<-getOneParam pn rhs
            let p = getOneParam pn rhs1
            -- putStrLn (show p)
            if (nonEmptyList p) then do rhs' <- rmOneParam pn rhs1
                                        allParams pn rhs' (initial++[p])
                     else return initial
        where
           getOneParam :: (SYB.Data t) => GHC.Name -> t -> [GHC.HsExpr GHC.Name]
           getOneParam pn1
              = SYB.everythingStaged SYB.Renamer (++) []
                   ([] `SYB.mkQ`  worker)
              -- =applyTU (stop_tdTU (failTU `adhocTU` worker))
                where
                  worker :: GHC.HsExpr GHC.Name -> [GHC.HsExpr GHC.Name]
                  worker (GHC.HsApp e1 e2)
                   |(expToName e1==pn1) = [GHC.unLoc e2]
                  worker _ = []
           rmOneParam :: (SYB.Data t) => GHC.Name -> t -> RefactGhc t
           rmOneParam pn1 t
              -- This genuinely needs to be done once only. Damn.
              -- =applyTP (stop_tdTP (failTP `adhocTP` worker))
             = do
                -- _ <- clearRefactDone
                everywhereMStaged' SYB.Renamer (SYB.mkM worker) t
                where
                  {-
                  worker :: GHC.HsExpr GHC.Name -> RefactGhc (GHC.HsExpr GHC.Name)
                  worker e@(GHC.HsApp e1 e2 ) = do -- The param being removed is e2
                    done <- getRefactDone
                    case (not done) && expToName e1==pn1 of
                      True ->  do setRefactDone
                                  return (GHC.unLoc e1)
                      False -> return e
                  worker x = return x
                  -}
                  worker (GHC.HsApp e1 _e2 ) -- The param being removed is e2
                    |expToName e1==pn1 = return (GHC.unLoc e1)
                  worker x = return x
{-
              AST output

                 addthree x y z

              becomes

                  (HsApp
                    (L {test/testdata/Demote/WhereIn6.hs:10:17-28}
                     (HsApp
                      (L {test/testdata/Demote/WhereIn6.hs:10:17-26}
                       (HsApp
                        (L {test/testdata/Demote/WhereIn6.hs:10:17-24}
                         (HsVar {Name: WhereIn6.addthree}))
                        (L {test/testdata/Demote/WhereIn6.hs:10:26}
                         (HsVar {Name: x}))))
                      (L {test/testdata/Demote/WhereIn6.hs:10:28}
                       (HsVar {Name: y}))))
                    (L {test/testdata/Demote/WhereIn6.hs:10:30}
                     (HsVar {Name: z})))

-----
                  (HsApp
                     (HsApp
                       (HsApp
                         (HsVar {Name: WhereIn6.addthree}))
                         (HsVar {Name: x}))))
                       (HsVar {Name: y}))))
                     (HsVar {Name: z})))

-----

                  sq p x

               becomes

                  (HsApp
                   (HsApp
                     (HsVar {Name: Demote.WhereIn4.sq}))
                     (HsVar {Name: p}))))
                   (HsVar {Name: x})))

----
                  sq x

               becomes

                  (HsApp
                   (HsVar {Name: sq}))
                   (HsVar {Name: x})))
-}


       -----------remove parameters in demotedDecls-------------------------------
       rmParamsInDemotedDecls :: [GHC.Name] -> GHC.HsBind GHC.Name
                              -> RefactGhc (GHC.HsBind GHC.Name)
       rmParamsInDemotedDecls ps bind
         -- = error $ "rmParamsInDemotedDecls: (ps,bind)=" ++ (showGhc (ps,bind)) -- ++AZ++
         -- =applyTP (once_tdTP (failTP `adhocTP` worker))
         = everywhereMStaged SYB.Renamer (SYB.mkM worker) bind
            -- where worker ((HsMatch loc1 name pats rhs ds)::HsMatchP)
            where worker (GHC.Match pats2 typ rhs1)
                    = do
                         let pats'=filter (\x->not ((patToPNT x /= Nothing) &&
                                          elem (gfromJust "rmParamsInDemotedDecls" $ patToPNT x) ps)) pats2

                         let (startPos,endPos) = getBiggestStartEndLoc pats2
                         if (emptyList pats')
                           then removeToksForPos (startPos,endPos)
                           else -- updateToksWithPos (startPos,endPos) pats' prettyprint False
                                updateToksWithPos (startPos,endPos) pats' pprPat False

                         -- pats'' <- update pats pats' pats

                         return (GHC.Match pats' typ rhs1)

       pprPat pat = intercalate " " $ map (\p -> (prettyprint p )) pat

       ----------remove parameters in the parent functions' rhs-------------------
       --Attention: PNT i1 _ _==PNT i2 _ _ = i1 =i2
       rmParamsInParent :: GHC.Name -> [GHC.HsExpr GHC.Name] -> GHC.GRHSs GHC.Name
                        -> RefactGhc (GHC.GRHSs GHC.Name)
       rmParamsInParent pn es
         -- =applyTP (full_buTP (idTP `adhocTP` worker))
         = everywhereMStaged SYB.Renamer (SYB.mkM worker)
            where worker expr@(GHC.L _ (GHC.HsApp e1 e2))
                   -- was | findPN pn e1 && (elem (GHC.unLoc e2) es)
                   | findPN pn e1 && (elem (showGhc (GHC.unLoc e2)) (map (showGhc) es))
                      = update expr e1 expr
                  worker (expr@(GHC.L _ (GHC.HsPar e1)))
                    |pn==expToName e1
                       = update expr e1 expr
                  worker x =return x


       getClashedNames oldNames newNames match
         = do  (_f,d) <- hsFDsFromInside match
               -- ds' <- mapM (flip hsVisiblePNs match) oldNames
               ds' <- mapM (flip hsVisiblePNs match) oldNames
               -- return clashed names
               return (filter (\x->elem ({- pNtoName -} x) newNames)  --Attention: nub
                                   ( nub (d `union` (nub.concat) ds')))

       ----- make Substitions between formal and actual parameters.-----------------
       mkSubst :: [GHC.LPat GHC.Name] -> [[GHC.HsExpr GHC.Name]] -> [(GHC.Name,GHC.HsExpr GHC.Name)]
       mkSubst pats1 params
           = catMaybes (zipWith (\x y -> if (patToPNT x/=Nothing) && (length (nub $ map showGhc y)==1)
                                          then Just (gfromJust "mkSubst" $ patToPNT x,(ghead "mkSubst") y)
                                          else Nothing) pats1 params)


-- |substitute an old expression by new expression
replaceExpWithUpdToks :: (SYB.Data t)
                      => t -> (GHC.Name, GHC.HsExpr GHC.Name)
                      -> RefactGhc t
replaceExpWithUpdToks  decls subst
  -- = applyTP (full_buTP (idTP `adhocTP` worker)) decls
  = everywhereMStaged' SYB.Renamer (SYB.mkM worker) decls
         where worker (e@(GHC.L l _)::GHC.LHsExpr GHC.Name)
                 |(expToName e/=defaultName) &&  (expToName e)==(fst subst)
                     = update e (GHC.L l (snd subst)) e
               worker x=return x


-- | return True if pn is a local function/pattern name
isLocalFunOrPatName :: SYB.Data t => GHC.Name -> t -> Bool
isLocalFunOrPatName pn scope
 = isLocalPN pn && isFunOrPatName pn scope

-- ---------------------------------------------------------------------

-- |Divide a declaration list into three parts (before, parent, after)
-- according to the PNT, where 'parent' is the first decl containing
-- the PNT, 'before' are those decls before 'parent' and 'after' are
-- those decls after 'parent'.

divideDecls ::
  SYB.Data t =>
  [t] -> GHC.Located GHC.Name -> ([t], [t], [t])
divideDecls ds pnt
  -- = error "undefined divideDecls"
  = let (before,after)=break (\x->findPNT pnt x) ds
    in if (not $ emptyList after)
         then (before, [ghead "divideDecls" after], tail after)
         else (ds,[],[])
