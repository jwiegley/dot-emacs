{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.Haskell.Refact.Refactoring.DupDef(duplicateDef) where

import qualified Data.Generics as SYB
import qualified GHC.SYB.Utils as SYB

import qualified GHC
import qualified OccName               as GHC

import Control.Monad
import Data.List
import Data.Maybe

import Language.Haskell.GhcMod
import Language.Haskell.Refact.API


-- ---------------------------------------------------------------------
-- | This refactoring duplicates a definition (function binding or
-- simple pattern binding) at the same level with a new name provided by
-- the user. The new name should not cause name clash/capture.
duplicateDef :: RefactSettings -> Cradle -> FilePath -> String -> SimpPos -> IO [FilePath]
duplicateDef settings cradle fileName newName (row,col) =
  runRefacSession settings cradle (comp fileName newName (row,col))

comp :: FilePath -> String -> SimpPos
     -> RefactGhc [ApplyRefacResult]
comp fileName newName (row, col) = do
      if isVarId newName
        then do
                getModuleGhc fileName
                renamed <- getRefactRenamed
                parsed  <- getRefactParsed

                let (Just (modName,_)) = getModuleName parsed
                let maybePn = locToName (row, col) renamed
                case maybePn of
                  Just pn ->
                       do
                          -- refactoredMod@((_fp,ismod),(_toks',renamed')) <- applyRefac (doDuplicating pn newName) (Just modInfo) fileName
                          (refactoredMod@((_fp,ismod),(_,_toks',renamed')),_) <- applyRefac (doDuplicating pn newName) (RSFile fileName)
                          case (ismod) of
                            False -> error "The selected identifier is not a function/simple pattern name, or is not defined in this module "
                            True -> return ()

                          if modIsExported modName renamed
                           then do clients <- clientModsAndFiles modName
                                   logm ("DupDef: clients=" ++ (showGhc clients)) -- ++AZ++ debug
                                   refactoredClients <- mapM (refactorInClientMod (GHC.unLoc pn) modName 
                                                             (findNewPName newName renamed')) clients
                                   return $ refactoredMod:refactoredClients
                           else  return [refactoredMod]
                  Nothing -> error "Invalid cursor position!"
        else error $ "Invalid new function name:" ++ newName ++ "!"



doDuplicating :: GHC.Located GHC.Name -> String
              -> RefactGhc ()
doDuplicating pn newName = do
   inscopes <- getRefactInscopes
   renamed  <- getRefactRenamed
   reallyDoDuplicating pn newName inscopes renamed


reallyDoDuplicating :: GHC.Located GHC.Name -> String
              -> InScopes -> GHC.RenamedSource
              -> RefactGhc ()
reallyDoDuplicating pn newName inscopes renamed = do

   renamed' <- everywhereMStaged SYB.Renamer (SYB.mkM dupInMod
                                  `SYB.extM` dupInMatch
                                  `SYB.extM` dupInPat
                                  `SYB.extM` dupInLet
                                  `SYB.extM` dupInLetStmt
                                 ) renamed
   putRefactRenamed renamed'
   return ()

        where
        --1. The definition to be duplicated is at top level.
        -- dupInMod :: (GHC.HsGroup GHC.Name)-> RefactGhc (GHC.HsGroup GHC.Name)
        dupInMod (grp :: (GHC.HsGroup GHC.Name))
          | not $ emptyList (findFunOrPatBind pn (hsBinds grp)) = doDuplicating' inscopes grp pn
        dupInMod grp = return grp

        --2. The definition to be duplicated is a local declaration in a match
        dupInMatch (match@(GHC.Match _pats _typ rhs)::GHC.Match GHC.Name)
          | not $ emptyList (findFunOrPatBind pn (hsBinds rhs)) = doDuplicating' inscopes match pn
        dupInMatch match = return match

        --3. The definition to be duplicated is a local declaration in a pattern binding
        dupInPat (pat@(GHC.PatBind _p rhs _typ _fvs _) :: GHC.HsBind GHC.Name)
          | not $ emptyList (findFunOrPatBind pn (hsBinds rhs)) = doDuplicating' inscopes pat pn
        dupInPat pat = return pat

        --4: The defintion to be duplicated is a local decl in a Let expression
        dupInLet (letExp@(GHC.HsLet ds _e):: GHC.HsExpr GHC.Name)
          | not $ emptyList (findFunOrPatBind pn (hsBinds ds)) = doDuplicating' inscopes letExp pn
        dupInLet letExp = return letExp

        --5. The definition to be duplicated is a local decl in a case alternative.
        -- Note: The local declarations in a case alternative are covered in #2 above.

        --6.The definition to be duplicated is a local decl in a Let statement.
        dupInLetStmt (letStmt@(GHC.LetStmt ds):: GHC.Stmt GHC.Name)
           -- was |findFunOrPatBind pn ds /=[]=doDuplicating' inscps letStmt pn
           |not $ emptyList (findFunOrPatBind pn (hsBinds ds)) = doDuplicating' inscopes letStmt pn
        dupInLetStmt letStmt = return letStmt


        -- findFunOrPatBind :: (SYB.Data t) => GHC.Located GHC.Name -> t -> [GHC.LHsBind GHC.Name]
        findFunOrPatBind (GHC.L _ n) ds = filter (\d->isFunBindR d || isSimplePatBind d) $ definingDeclsNames [n] ds True False


        doDuplicating' :: (HsValBinds t) => InScopes -> t -> GHC.Located GHC.Name
                       -> RefactGhc (t)
        doDuplicating' _inscps parentr ln@(GHC.L _ n)
           = do let
                    declsr = hsBinds parentr

                    duplicatedDecls = definingDeclsNames [n] declsr True False
                    -- (after,before)  = break (definesP pn) (reverse declsp)

                (f,d) <- hsFDNamesFromInside parentr
                    --f: names that might be shadowd by the new name,
                    --d: names that might clash with the new name

                dv <- hsVisibleNames ln declsr --dv: names may shadow new name
                let vars        = nub (f `union` d `union` dv)

                newNameGhc <- mkNewGhcName Nothing newName
                -- TODO: Where definition is of form tup@(h,t), test each element of it for clashes, or disallow
                nameAlreadyInScope <- isInScopeAndUnqualifiedGhc newName Nothing

                -- logm ("DupDef: nameAlreadyInScope =" ++ (show nameAlreadyInScope)) -- ++AZ++ debug
                -- logm ("DupDef: ln =" ++ (show ln)) -- ++AZ++ debug

                if elem newName vars || (nameAlreadyInScope && findEntity ln duplicatedDecls) 
                   then error ("The new name'"++newName++"' will cause name clash/capture or ambiguity problem after "
                               ++ "duplicating, please select another name!")
                   else do newBinding <- duplicateDecl declsr parentr n newNameGhc
                           -- let newDecls = replaceDecls declsr (declsr ++ newBinding)
                           let newDecls = replaceBinds declsr (declsr ++ newBinding)
                           return $ replaceBinds parentr newDecls



-- | Find the the new definition name in GHC.Name format.
findNewPName :: String -> GHC.RenamedSource -> GHC.Name
findNewPName name renamed = gfromJust "findNewPName" res
  where
     res = somethingStaged SYB.Renamer Nothing
            (Nothing `SYB.mkQ` worker) renamed

     worker  (pname::GHC.Name)
        | (GHC.occNameString $ GHC.getOccName pname) == name = Just pname
     worker _ = Nothing


-- | Do refactoring in the client module. That is to hide the
-- identifer in the import declaration if it will cause any problem in
-- the client module.
refactorInClientMod :: GHC.Name -> GHC.ModuleName -> GHC.Name -> TargetModule
                    -> RefactGhc ApplyRefacResult
refactorInClientMod oldPN serverModName newPName targetModule@(_,modSummary)
  = do
       logm ("refactorInClientMod: (serverModName,newPName)=" ++ (showGhc (serverModName,newPName))) -- ++AZ++ debug
       void $ activateModule targetModule

       let fileName = gfromJust "refactorInClientMod" $ GHC.ml_hs_file $ GHC.ms_location modSummary
{-
       -- modInfo@(t,ts) <- getModuleGhc fileName
       getModuleGhc fileName
-}
       renamed <- getRefactRenamed
       parsed <- getRefactParsed

       let modNames = willBeUnQualImportedBy serverModName renamed
       logm ("refactorInClientMod: (modNames)=" ++ (showGhc (modNames))) -- ++AZ++ debug

       -- if isJust modNames && needToBeHided (pNtoName newPName) exps parsed
       mustHide <- needToBeHided newPName renamed parsed
       logm ("refactorInClientMod: (mustHide)=" ++ (showGhc (mustHide))) -- ++AZ++ debug
       if isJust modNames && mustHide
        then do
                -- refactoredMod <- applyRefac (doDuplicatingClient serverModName [newPName]) (Just modInfo) fileName
                (refactoredMod,_) <- applyRefac (doDuplicatingClient serverModName [newPName]) (RSFile fileName)
                return refactoredMod
        else return ((fileName,unmodified),([],[],renamed))
   where
     needToBeHided :: GHC.Name -> GHC.RenamedSource -> GHC.ParsedSource -> RefactGhc Bool
     needToBeHided name exps parsed = do
         let usedUnqual = usedWithoutQualR name parsed
         logm ("refactorInClientMod: (usedUnqual)=" ++ (showGhc (usedUnqual))) -- ++AZ++ debug
         return $ usedUnqual || causeNameClashInExports oldPN name serverModName exps

doDuplicatingClient :: GHC.ModuleName -> [GHC.Name]
              -> RefactGhc ()
doDuplicatingClient serverModName newPNames = do
  renamed  <- getRefactRenamed
  renamed' <- addHiding serverModName renamed newPNames
  putRefactRenamed renamed'
  return ()



--Check here:
-- | get the module name or alias name by which the duplicated
-- definition will be imported automatically.
willBeUnQualImportedBy :: GHC.ModuleName -> GHC.RenamedSource -> Maybe [GHC.ModuleName]
willBeUnQualImportedBy modName (_,imps,_,_)
   = let
         ms = filter (\(GHC.L _ (GHC.ImportDecl (GHC.L _ modName1) _qualify _source _safe isQualified _isImplicit _as h))
                    -> modName == modName1
                       && not isQualified
                              && (isNothing h  -- not hiding
                                  ||
                                   (isJust h && ((fst (gfromJust "willBeUnQualImportedBy" h))==True))
                                  ))
                      imps
         in if (emptyList ms) then Nothing
                      else Just $ nub $ map getModName ms

         where getModName (GHC.L _ (GHC.ImportDecl _modName1 _qualify _source _safe _isQualified _isImplicit as _h))
                 = if isJust as then (fromJust as)
                                else modName
               -- simpModName (SN m loc) = m

