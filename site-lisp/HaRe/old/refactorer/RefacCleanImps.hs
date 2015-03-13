

module RefacCleanImps(cleanImports,mkImpExplicit,addToExport,rmFromExport) where

import PosSyntax
import Data.Maybe
import TypedIds
import Data.List hiding (delete)
import RefacUtils
import UniqueNames hiding (srcLoc)
import HsName hiding (ModuleName)
import SourceNames
import PNT
import RefacMoveDef(liftingInClientMod)
import PFE0 (findFile)
import PrettyPrint hiding (group)
import NamesEntities
import Ents
import Relations
import Modules(mImp',mExpListEntry)
import AST4ModSys (toImport',toExpListEntry')
import HsIdent(HsIdentI(..))


{- This refactoring trys to remove the unnecessary import declarations from the module-}

cleanImports args
 = do let fileName= ghead "filename" args
      (inscps, _, mod'', toks) <- parseSourceFile fileName
      let mod = rmPrelude mod''
          inscps' =relToList inscps
      imp_Ents_List <- getImportedEnts inscps' (hsModImports mod)
      (mod',((toks',m),_))<-runStateT (doCleanImports imp_Ents_List (inscps', mod))
                                        ((toks,unmodified),(-1000,0))
      writeRefactoredFiles False [((fileName,m),(toks', mod'))]


doCleanImports imp_Ents_List (inscps, mod@(HsModule _ modName exps imps decls))
 = do  -- imp_usedEnts_List ::[(ImportDeclP, [PNames])]
      let imp_usedEnts_List =map (getUsedEnts mod) imp_Ents_List
      mod' <- checkEachImport mod (imp_usedEnts_List, imp_usedEnts_List)
      combineImports mod' (hsModImports mod')

-- remove an import declaration from the module.
rmOneImport mod@(HsModule loc modName exps imps decls) imp
  = do imps' <- delete imp imps
       return (HsModule loc modName exps (imps\\[imp]) decls)


checkEachImport mod@(HsModule loc modName exps imps decls) ([],_)
  =return mod

checkEachImport mod@(HsModule loc modName exps imps decls) ((i@(imp,inscpEnts,usedEnts):is), origList)
  = if usedEnts == []   -- this import decl is not used at all.
      then do mod'<- (do m'<-rmOneImport mod imp
                         if inscpEnts==[] && modIsExported1 (qualifier imp) mod
                           then rmItemsFromExport m' (Left ([qualifier imp], []))
                           else return m')
              checkEachImport mod' (is, (origList \\ [i]))
      else if any (\(x,y,z)->(usedEnts == z  && length inscpEnts >= length y)
                    || (usedEnts \\ z ==[] && length usedEnts <length z)) (origList \\ [i])
             then do mod'<-rmOneImport mod imp
                     checkEachImport mod' (is,(origList \\[i]))
             else checkEachImport mod (is, origList)


--getImportedEnts::[(QName,Entity)]->[HsImportDeclP]->[(HsImportDeclP,[(QName,Entity)])]
getImportedEnts inscps imps
 = do importedEnts<-mapM getImportedEnts' imps
      return $ zip imps importedEnts
  where
    getImportedEnts' (imp@(HsImportDecl loc (SN modName _) qual as h)::HsImportDeclP)
       = do fileName <- PFE0.findFile modName
            (_, exps, mod, toks) <- parseSourceFile fileName
            return $ relToList (mImp' (listToRel exps)
                     (toImport' (HsImportDecl loc modName qual (as' as) h)))
      where as' Nothing = Nothing
            as' (Just (SN modName _)) = Just modName

getUsedEnts mod@(HsModule _ _ exps imps decls) (imp@(HsImportDecl _ (SN modName _) _ as h),inscpEnts)
  = if modIsExported1 (qualifier imp) mod
      then (imp, inscpEnts, inscpEnts)
      else case h of
              (Just (False, ents)) ->if ents == []
                                       then (imp, inscpEnts,[])
                                       else (imp, inscpEnts, usedEnts' (exps, decls))
              _ -> (imp, inscpEnts, usedEnts' (exps, decls))
   where
     usedEnts'= (nub.ghead "getUsedEnts'"). applyTU (full_tdTU (constTU [] `adhocTU` inPnt))
        where
          inPnt pnt@(PNT pname ty loc)
           | isTopLevelPNT pnt
            =let ent'=pntToEnt pnt
             in if isJust (find (==ent') inscpEnts)
                  then return [ent']
                  else return []
          inPnt _ = return []

--- THIS FUNCTION SHOULD GO TO THE API.
modIsExported1 modName mod
 = if isNothing exps
     then False
     else isJust $ find (\x->getModName x == Just modName) (fromJust exps)
   where
     exps =  hsModExports mod
     getModName (ModuleE  (SN modName _)) = Just modName
     getModName _ = Nothing


unqualify ((SN (Qual _ id) l), ent) = ((SN (UnQual id) l), ent)
unqualify x  = x

qualifier (HsImportDecl _ (SN modName _) qual Nothing h) = modName
qualifier (HsImportDecl _ _ qual (Just (SN modName _)) h) = modName

combineImports mod [] = return mod
combineImports mod@(HsModule _ _ _ imps _) (i:is)
   = case i of
     (HsImportDecl _ modName@(SN modName' _)  qual as (Just(False, ents)))
        ->let sub_is= filter (\x-> case x of
                                  (HsImportDecl _ modName1 qual1 as1 (Just(False,ents1)))
                                    ->modName1 == modName && qual==qual1 && as == as1
                                  _ ->False ) is
          in if sub_is==[] then combineImports mod is
                           else do let ents=concatMap importedEnts sub_is
                                   mod'<-foldM rmOneImport mod sub_is
                                   let (imps1, imps2) = break (==i) imps
                                   i' <-addItemsToImport modName' Nothing (Right ents) i
                                   combineImports (mod' {hsModImports =((imps1++[i']++(tail imps2)) \\ sub_is)}) (is \\ sub_is)
     _  ->combineImports mod is
  where
     importedEnts (HsImportDecl _ _ False Nothing (Just(False,ents))) =ents
     importedEnts  _ =[]

pntToEnt pnt@(PNT pn@(PN (UnQual s) (G modName s1 loc)) ty _)
  = let t= if hasNameSpace pnt == ValueName then HsVar else HsCon
    in ((SN (UnQual s) (getSrcLoc loc)), (Ent modName (t (SN s (getSrcLoc loc))) (fmap pIdtoId ty)))

pntToEnt pnt@(PNT pn@(PN (Qual modName s) (G modName1 s1 loc)) ty _)
  = let t= if hasNameSpace pnt == ValueName then HsVar else HsCon
    in ((SN (Qual modName s) (getSrcLoc loc)) , (Ent modName1 (HsVar (SN s (getSrcLoc loc))) (fmap pIdtoId ty)))

pIdtoId pn@(PN i orig) = (SN i (srcLoc pn))

getSrcLoc (N (Just loc)) = loc
getSrcLoc (N Nothing)    = loc0

-- this refactoring makes the all the used enitities from a import decl explicit in the import declaration.
mkImpExplicit args
 =do let fileName= ghead "filename" args
         row = read (args!!1)::Int
         col = read (args!!2)::Int
     modName <- fileNameToModName fileName
     (inscps, _, mod, toks) <- parseSourceFile fileName
     let imp'=locToImport fileName row col mod
     unless (isJust imp')
        $ error ("Invalid cursor position! "++
                "Please point the cursor to the beginning position of the module name." )
     let inscps' = relToList inscps
         imp = fromJust imp'
     [(imp, importedEnts)] <- getImportedEnts inscps' [imp]
     (mod',((toks',_),_))<-runStateT (doExplicitImport mod (imp,importedEnts))
                                         ((toks,unmodified),(-1000,0))
     writeRefactoredFiles False [((fileName,True),(toks', mod'))]


locToImport fileName row col mod
  = applyTU (once_buTU (failTU `adhocTU` worker)) mod
      where
       worker (imp@(HsImportDecl l (SN modName (SrcLoc _ _ row1 col1)) _ _ _)::HsImportDeclP)
         | row1 == row && col1 == col
         =Just imp
       worker _ = Nothing

doExplicitImport mod (imp@(HsImportDecl l m qual as _),importedEnts)
 = do let used =usedEnts importedEnts  mod
          (imps1, imps2) = break (==imp) (hsModImports mod)
      imp' <-update imp ( if (used==[])  then (HsImportDecl l m qual as (Just(False, [])))
                                         else (HsImportDecl l m qual as (Just (False, used)))) imp
      return (mod {hsModImports=(imps1++[imp']++imps2)})

  where
   usedEnts importedEnts = combineEntSpecs. (nub.ghead "usdEnts'").
                            applyTU (full_tdTU (constTU [] `adhocTU` inPnt))
        where
          inPnt pnt@(PNT pname ty loc)
           | isTopLevelPNT pnt
            =let ent'=pntToEnt pnt
             in if isJust (find (==ent') importedEnts)
                  then return [pNTtoEntSpec pnt]
                  else return []
          inPnt _ = return []

   combineEntSpecs [] = []
   combineEntSpecs (e:es)
       = case e of
          Abs pnt -> if findDup pnt es then combineEntSpecs es else (e:combineEntSpecs es)
               where findDup pnt es = any (\x->case x of
                                            ListSubs i is -> pNTtoName i== pNTtoName pnt
                                            Abs  i        -> pNTtoName i== pNTtoName pnt
                                            _             -> False) es
          ListSubs p _ -> if findDup p es then combineEntSpecs (doCombine e es)  else (e:combineEntSpecs es)
              where findDup pnt es = any (\x->case x of
                                              ListSubs p' _ ->pNTtoName p == pNTtoName p'
                                              _  -> False) es
                    doCombine (ListSubs p cs) es
                          = let (es1, es2) = break (\x-> case x of
                                                    ListSubs p' _ ->pNTtoName p == pNTtoName p'
                                                    _ ->False) es
                                (ListSubs _ cs') = ghead "doCombine" es2
                            in (es1++[ListSubs p (cs++cs')]++tail es2)

          _  -> (e: combineEntSpecs es)

pNTtoEntSpec pnt@(PNT pn@(PN _ (G modName s1 loc)) ty _)
  = case  ty of
       ConstrOf i _ -> ListSubs (pIdToPNT i) [HsCon pnt']
       Type _       -> Abs pnt'
       _            -> Var pnt'
  where
   pIdToPNT (PN id orig) =PNT (PN (UnQual id) orig) Value  (N Nothing)

   pnt'= rmQualifier pnt
     where rmQualifier (PNT (PN (Qual modName  s) l) ty loc)= (PNT (PN (UnQual s) l) ty loc)
           rmQualifier  x  = x


-- this refactoring adds an user-selected top-level identifier to the export list.

addToExport args
 =do let fileName= ghead "filename" args
         row = read (args!!1)::Int
         col = read (args!!2)::Int
     modName <- fileNameToModName fileName
     (inscps, exps, mod, toks) <- parseSourceFile fileName
     let pnt = locToPNT fileName (row, col) mod
     unless (pnt/=defaultPNT) $ error "Invalid cursor position!\n"  -- this refactoring does not handle module names.
     unless (isTopLevelPNT pnt) $ error "The selected identifier is not a top level identifier!\n"
     (mod',((toks',_),_))<-runStateT (doAddingToExport pnt mod)
                                         ((toks,unmodified),(-1000,0))
     clients <-clientModsAndFiles modName
     refactoredClients <-mapM (refactorInClientMod modName (pNTtoPN pnt)) clients
     writeRefactoredFiles False $ ((fileName,True),(toks', mod')):refactoredClients
  where
     doAddingToExport pnt mod
      = do let pn = pNTtoPN pnt
           unless (not (isExplicitlyExported pn mod  || modIsExported mod))
                   $ error "The indentifier is already exported!\n"
           let exps=fromJust $ hsModExports mod
               newEnt = EntE (pNTtoEntSpec pnt)
           insertEEnt mod newEnt

     insertEEnt mod e@(EntE ent)
      = let exps = fromJust $ hsModExports mod
        in case  ent  of
            ListSubs i is  ->
               let (exps1,exps2)=break (\i'->case i' of
                                             (EntE (ListSubs i'' _)) ->(i''==i)
                                             (EntE (Abs i''))        ->(i''== i)
                                             _                       -> False) exps
               in if exps2 == []
                   then do addItemsToExport mod Nothing False (Right [e])
                           return $ (mod {hsModExports=Just ([e]++exps)})
                   else do let e'=ghead "insertEnt" exps2
                           exps'<- case e' of
                                    (EntE (ListSubs i'' is')) ->
                                        do e''<-update e' (EntE (ListSubs i (is'++is))) e'
                                            -- there is a problem with pretty-printing (EntE ...)
                                           return $ Just (exps1++(e'':tail exps2))
                                    (EntE (Abs i'')) ->
                                        do e''<-update  e'(EntE (ListSubs i'' is)) e'
                                           return $ Just (exps1 ++(e'':tail exps2))
                           return $ (mod {hsModExports=exps'})
            _  -> do addItemsToExport mod Nothing False (Right [e])
                     return $ (mod {hsModExports=Just ([e]++exps)})

     refactorInClientMod serverModName pn (modName, fileName)
       = liftingInClientMod serverModName [pn] (modName, fileName)

--This refactoring removes an user-selected entry from the export list if none of the idenitifiers exported
--by this entry is used by other modules.

-- NOTE: This refactoring DOES NOT HANDLE SUB-ENTRIES in the export list. (Can this be improved?)

rmFromExport args
 =do let fileName= ghead "filename" args
         row = read (args!!1)::Int
         col = read (args!!2)::Int
     modName <- fileNameToModName fileName
     (inscps, exps, mod, toks) <- parseSourceFile fileName
     let eEntry' = locToEEntry row col mod toks
     unless (eEntry'/=Nothing) $ error "Invalid cursor position!\n"
     let eEntry = fromJust eEntry'
         ents = exportedEnts inscps eEntry
     if isDuplicatedEntry inscps (eEntry, ents) (fromJust (hsModExports mod))
       then do (mod',((toks',m),_))<-runStateT (doRmFromExport mod eEntry)
                                   ((toks,unmodified),(-1000,0))
               writeRefactoredFiles False [((fileName, m),(toks',mod'))]
       else do clients<-clientModsAndFiles modName
               refactoredClients <- mapM (refactorInClientMod ents) clients
               (mod',((toks',m),_))<-runStateT (doRmFromExport mod eEntry)
                                        ((toks,unmodified),(-1000,0))
               writeRefactoredFiles False $ ((fileName,m),(toks',mod')):refactoredClients


   where

    -- Calculates all the entities exported by this entry.
    exportedEnts inscps eEntry = relToList (mExpListEntry inscps  (toExpListEntry' eEntry))

    -- Returns True if this entry is duplicated or covered by another entry in the export list.
    isDuplicatedEntry inscps (eEntry, ents) exps
       =let ents'= map (mExpListEntry' inscps) (map toExpListEntry' (exps \\[eEntry]))
        in  any (\e->intersect e ents==ents) ents'
        where mExpListEntry' inscps entry= relToList (mExpListEntry inscps entry)

    -- Removes an entry from the export list.
    doRmFromExport mod eEntry = rmItemsFromExport mod (Right [eEntry])

    -- get the user selected entry from the export list.
    locToEEntry row col mod toks
      =if isJust exps
          then let (_, e2) =break (\e->let (startLoc, endLoc) =getStartEndLoc toks e
                                       in startLoc<=(row,col) && (row,col)<=endLoc) (fromJust exps)
               in if e2==[] then Nothing else Just (head e2)
           else Nothing

       where exps = hsModExports mod

    refactorInClientMod ents (modName, fileName)
      = do (inscps, exps, mod ,ts) <-parseSourceFile fileName
           -- The following condition is too strong.
           if findEnt ents (hsModDecls mod) || (intersect (map impEntToExpEnt ents) exps) /= []
            then  error $ "This entity can not be removed as it is used by the client module '"++(render.ppi) modName++"'!"
            else do let pnsToBeHided =findPns ents (hsModImports mod)
                    if pnsToBeHided/=[]
                     then do (mod', ((ts',m),_))<-runStateT (rmItemsFromImport mod pnsToBeHided)
                                                   ((ts,unmodified),(-1000,0))
                             return ((fileName,m), (ts',mod'))
                     else return ((fileName,unmodified), (ts,mod))
    findEnt ents
        = (fromMaybe False).(applyTU (once_tdTU (failTU `adhocTU` worker)))
          where
            worker (pnt::PNT)
             |isTopLevelPNT pnt && isJust (find (==(pntToEnt pnt)) ents) = Just True
            worker _ = Nothing

    impEntToExpEnt ((SN (UnQual s) loc1), e) = ((SN s loc1), e)
    impEntToExpEnt ((SN (Qual modName s) loc1),e) = ((SN s loc1), e)

    findPns ents
        = (nub.ghead "findPns").(applyTU (full_tdTU (constTU [] `adhocTU` worker)))
          where
            worker (pnt::PNT)
             |isTopLevelPNT pnt && isJust (find (==(pntToEnt pnt)) ents) = return [pNTtoPN pnt]
            worker _ = return []

