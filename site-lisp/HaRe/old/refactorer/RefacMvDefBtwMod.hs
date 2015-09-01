

-- ++AZ++ addImport is new since 0.6.0.2
module RefacMvDefBtwMod(moveDefBtwMod, addImport) where

import Data.Maybe
import Data.List
import RefacUtils  hiding (getQualifier)
import PFE0 (findFile)
import PrettyPrint
import Debug.Trace
import Data.List ((\\))

{-This refactoring moves a user-selected function definition/pattern binding from current module to a
  user specified module.
  To perform this refactoring: put the cursor at the begining of the function/pattern name, then select
  the 'moveDefBtwMod' menu from the 'refactor' menu, and input the target module name in the mini-buffer
  as prompted.-}

moveDefBtwMod args
 = do let fileName     = ghead "filename" args
          destModName' = args!! 1
          destModName  = strToModName destModName'  -- there may be problem with the main module
          row          = read (args!!2)::Int
          col          = read (args!!3)::Int
      origModName <- fileNameToModName fileName
      r <-isAnExistingMod destModName
      unless r $  error "The specified module does not exist!"
      unless (origModName /= destModName) $ error "The target module name is the same as the current module name!"
      (origInscps, _, origMod, origToks) <- parseSourceFile fileName
      let pn = pNTtoPN $ locToPNT fileName (row, col) origMod
          decl =definingDecls [pn] (hsModDecls origMod) False True
      unless (pn /= defaultPN)
         $ error "Invalid cursor position. Please point the cursor to the beginning of the function/pattern name!"
      unless (isTopLevelPN pn && decl/=[]) $ error "The selected definition is not a top-level function/pattern definition!"
      -- Find the file name of the target module.
      destFile<-PFE0.findFile destModName
      -- Parse the target module.
      (destInscps, _, destMod, destToks) <-parseSourceFile destFile
      -- get the pnames defined by the declaration to be moved.
      let pns  = nub $ concatMap definedPNs decl
      -- get the subset of 'pns' which are already defined in the target module.
      namesDefined <- namesDefinedIn (map pNtoName pns)  destMod
      unless (namesDefined == [] )
           (if length namesDefined == 1
               then error ("The function/pattern name: " ++ show (head (namesDefined))
                    ++ " is already defined in module "++ destModName'++ " !")
               else error ("The pattern names: " ++ show namesDefined ++ " are already defined in module " ++ destModName'++ " !"))
      -- Get the client modules and the corresponding file names of the original module.
      clientsOfOrigMod <- clientModsAndFiles =<< RefacUtils.fileNameToModName fileName
      -- Get the client modules and the corresponding file names of the original module.
      clientsOfDestMod <- clientModsAndFiles =<< RefacUtils.fileNameToModName destFile
      -- get the free variables in the definition to be moved.
      freePnts <- freePNTsIn pns decl
      let pnsNotInscope = varsNotInScope freePnts destInscps
      unless (pnsNotInscope == [])   -- why can not import these variables in the dest module?
          (if length pnsNotInscope == 1
             then error ("The free variable: '" ++ pNtoName (head pnsNotInscope)++
                      "', which is used by the definition to be moved is not in scope in the target module "++destModName' ++ " !")
             else error ("The free variables: " ++ showEntities pNtoName pnsNotInscope ++
                      ", which are used by the definition to be moved are not in scope in the target module " ++destModName' ++ " !"))
       -- Will the moving cause recursive modules?
      r <-causeRecursiveMods decl fileName origModName destModName
      unless (not r) $ error ("Moving the definition to module " ++ show destModName++ " will cause mutually recursive modules!")
      -- Remove the definition from the original module.
      (origMod', ((origToks',origM),_))<-rmCodeFromMod pns fileName (origMod, origToks) destModName destFile
      -- Parse all those client modules.
      let modsAndFiles=nub (clientsOfOrigMod++clientsOfDestMod) \\ [(origModName, fileName),(destModName, destFile)]
      parsedMods <-mapM parseSourceFile $ map snd modsAndFiles
      -- is the definition name used in modules other than the target module?
      let used = any (\(_,_,mod,_)->isUsedByMod pns mod) parsedMods  || isUsedByMod pns origMod
      -- Add the definition to the destination module.
      (destMod',((destToks',destM),_))<-addCodeToMod pns destFile (origMod, origToks)
                                        (destInscps,destModName,destMod, destToks) used
      --Do corrsponding modification in the client modules.
      refacClients <- mapM (refactorInClientMod origModName destModName pns) $ zip parsedMods $ map snd modsAndFiles

      -- output the result.
      writeRefactoredFiles False $ [((fileName,origM),(origToks',origMod')),
                                    ((destFile,destM),(destToks',destMod'))] ++ refacClients


-- Return the subset of 'names' that are defined in 't'.
namesDefinedIn  names t
  =do (_,rd)<-hsFreeAndDeclaredPNs t
      return ((map pNtoName rd) `intersect` names)

--Get those free variables (used by the definition to be moved) that are not in scope in the destination module.
varsNotInScope pnts inScopeRel
   = nub $ map pNTtoPN (filter
          (\pnt->if isQualifiedPN (pNTtoPN pnt) then  hsQualifier pnt inScopeRel == []
                                                else not (isInScopeAndUnqualified (pNTtoName pnt) inScopeRel)) pnts)

-- get those pnts which are free in 't' and not included in 'pns'
freePNTsIn pns t
 = do (pns', _) <- hsFDsFromInside t      -- Why not use freeAndDeclared?
      let pnts = nub $ hsPNTs =<< rmLocs t
      return $ filter (\t->elem  (pNTtoPN t) (pns' \\ pns)) pnts

--Return True if moving the definition from origMod to destMod will cause recursive modules.
causeRecursiveMods decl origFile origModName destModName
 =do let pns  = nub $ concatMap definedPNs decl
     clients<-clientModsAndFiles origModName
     servers <-serverModsAndFiles destModName
     let clientMods1 = map fst clients
         clientFiles =map snd clients
         serverMods = map fst servers
         serverFiles =map snd servers
     if elem destModName clientMods1
      then do let ms = origFile:(clientFiles `intersect` serverFiles)
              parsedMods<-mapM parseSourceFile ms
              let (_,_,origMod,_) = ghead "causeRecursiveMods" parsedMods
              return ( isUsedBy pns (hsDecls origMod \\ decl) ||
                       (any (\ (_,_,mod,_)->isUsedByMod pns mod) (tail parsedMods)))
      else if elem destModName serverMods
             then do clients <- clientModsAndFiles destModName
                     let ms = origModName : (map fst clients `intersect` serverMods)
                         r  = map fromJust (filter isJust (map hasModName $ nub (map pNTtoPN (hsPNTs decl)) \\ pns))
                     return $ any (\m-> elem m r ) ms
             else return False

isUsedByMod pns (HsModule _ _ _ _ ds) = isUsedBy pns ds

--Return True if any pname in 'pns' is used by 'mod'
isUsedBy pns t
   = fromMaybe False (applyTU (once_tdTU (failTU `adhocTU` worker)) t)
        where
         worker (pnt::PNT)
           | elem (pNTtoPN pnt) pns && isUsedInRhs pnt t
          = Just True
         worker _ = mzero


-- Remove the definition from the original module.

rmCodeFromMod pns fileName (mod, tokList) destModName destFileName
  = runStateT (do -- remove the definition.
                  decls'<-rmDecl (ghead "rmCodeFromMod"  pns) True (hsDecls mod)
                  -- remove the definition name from the export list
                  mod'<-rmItemsFromExport (replaceDecls mod decls') (Left ([],pns))
                  -- is the definition used in the current module?
                  if isUsedByMod pns mod'
                    then -- yes. add the definition name to the import.
                         do let qual=getQualifier destModName mod'
                            mod''<-replaceQualifier pns qual mod'
                            addImport destFileName destModName pns mod''
                    else --No, do nothing.
                         return mod')
             ((tokList,unmodified),(-1000,0))


-- Add the definition to the client module, and modify the import/export if necessary.
addCodeToMod  pns destFileName (origMod, origToks) (destInscps,destModName, destMod, destToks) usedByClients
 = do let -- get the declaraion. False means not spliting the type signature.
          decl  = definingDecls pns (hsDecls origMod) True False
           --get the fun binding.
          funBinding = ghead "addCodeToMod" $ filter isFunOrPatBind decl  -- shoudn't be empty.
           --get the type signature if there is any.
          typeSig    = filter isTypeSig decl
          decl' = if typeSig==[]
                    then [funBinding]
                    else [ghead "addCodeToMod" (getTypeSig pns (head typeSig)),funBinding]

          toksTobeAdded =getDeclToks (ghead "addCodeToMod" pns) True decl origToks
      (decl'', toksTobeAdded') <- if isDirectRecursiveDef funBinding &&
                                     sameNameInScope (ghead "addCodeToMod" pns) destInscps
                                  then do (t,((toks',_), m))<-runStateT (addQualifier pns modName decl)
                                                             ((toksTobeAdded,unmodified),(-1000,0))
                                          return (t, toks')
                                  else return (decl', toksTobeAdded)
      (decl''',((toksTobeAdded'',_),_)) <-runStateT (replaceQualifier pns destModName decl'')
                                          ((toksTobeAdded',unmodified),(-1000,0))  --destFileName)
      runStateT ( do  destMod'<-resolveAmbiguity pns destInscps destMod
                      mod'<-replaceQualifier pns destModName destMod'
                      mod''<- addDecl mod' Nothing (decl''', Just toksTobeAdded'') True
                      mod''' <- rmItemsFromImport mod'' pns
                      if usedByClients && not (modIsExported destMod)
                          -- The definition name is used by other modules, but it is
                         then addItemsToExport mod''' Nothing False (Right (map pnToEnt pns))   --so make it exported.
                         else return mod'''      -- Do nothing.
                ) ((destToks,unmodified), (-1000,0)) --destFileName)

   where
        -- Get the type signatures defines the type of pns.
       getTypeSig pns (Dec (HsTypeSig loc is c tp))
         =[(Dec (HsTypeSig loc (filter (\x->isJust (find (==pNTtoPN x) pns)) is) c tp))]
       getTypeSig pns _ = []

       modName = modNameToStr destModName

       pnToEnt pn = EntE (Var (pNtoPNT pn Value))


-- |Returns True if another identifier which has the same name but different meaning is in scope.
-- NOTE: The name space should be taken into account as well.
sameNameInScope::PName         -- ^ The identifier
                 ->InScopes    -- ^ The inscope relation
                 ->Bool        -- ^ The result
sameNameInScope pn inScopeRel = isJust $ find (\ (name, nameSpace, modName, _)-> name == pNtoName pn
                                                && hasModName pn /= Just modName ) $ inScopeInfo inScopeRel


-- modify the import interface in the client modules.
refactorInClientMod origModName destModName pns ((inscps, exps,mod, ts), fileName)
  = do (mod', ((ts',m),_)) <-
          runStateT ( do mod'<-rmItemsFromImport mod pns
                         mod''<- if isUsedByMod pns mod
                                  then do let qual=getQualifier destModName mod
                                          addImport fileName destModName pns =<< replaceQualifier pns qual mod'
                                  else if itemIsImportedByDefault destModName mod && causeAmbiguity pns mod'
                                         then addHiding destModName mod' pns
                                         else return mod'
                         return mod''
                    ) ((ts,unmodified),(-1000,0))
       return ((fileName,m),(ts',mod'))



--add a definition name to the import. If the module is not imported yet, then create a new import decl.
-- addImport::String->HsName.ModuleName->[PName]->HsModuleP->HsModuleP
addImport destFileName destModName pns mod@(HsModule _ _  _ imp _)
  =if itemIsImportedByDefault destModName mod     -- Is the definition name explicitly imported?
    then return mod                               -- Yes. Do nothing.
    else if itemsAreExplicitlyImported destModName mod  --Is the module imported and some of its items are explicitly imported?
          then addVarItemInImport1 destModName pns mod -- Yes. Then add the definition name to the list.
          else addImportDecl mod (modNameToStr destModName) False  Nothing False (map pNtoName pns)
               -- mod (mkImportDecl destFileName destModName  False (map pNtoName pns)) --Create a new import decl.

  where
   {- Compose a import declaration which imports the module specified by 'modName',
      and only imports the definition spcified by 'e'.
    -}
   --mkImportDecl::String->HsName.ModuleName->Bool->[HsName.Id]->HsImportDeclP
 {-  mkImportDecl fileName modName qual ids
     = (HsImportDecl loc0  (SN modName loc0)  qual Nothing (Just (False, (map makeEnt ids))))
      where
      makeEnt id= Var $ PNT (PN (UnQual id) (G modName id (N (Just loc0)))) Value (N (Just loc0)) -}

   itemsAreExplicitlyImported serverModName (HsModule _ _ _ imps _)
     = any (isExplicitlyImported serverModName) imps
    where
       isExplicitlyImported serverModName ((HsImportDecl _ (SN modName _) _ _ h)::HsImportDeclP)
         = serverModName == modName && isJust h && not (fst (fromJust h))



-- are items defined in the serverModName imported by the current module by default?
itemIsImportedByDefault serverModName (HsModule _ _ _ imps _)
  = any (isImportedByDefault'  serverModName) imps
  where
    isImportedByDefault' serverModName ((HsImportDecl _ (SN modName _) _ _ h)::HsImportDeclP)
       = serverModName == modName && ( isNothing h  || (isJust h && fst(fromJust h)))


addVarItemInImport1 serverModName pns mod
   = applyTP ((once_tdTP (failTP `adhocTP` inImport))  `choiceTP` idTP) mod
  where
    inImport (imp@(HsImportDecl loc@(SrcLoc fileName _ row col) (SN modName l) qual as (Just (b,ents))):: HsImportDeclP)
      | serverModName == modName && not b
     =  {-do let ents'= map (\pn->Var (pNtoPNT pn Value)) pns
           addItemsToImport1 imp ents'
           return (HsImportDecl loc (SN modName l) qual as (Just (b, (ents'++ents)))) -}
          let pns' = trace (show $ (pns, (map remVarPNT ents) )) (pns \\ (map remVarPNT ents))
              remVarPNT (Var x) = nameToPN (pNTtoName x)
          in
             addItemsToImport serverModName  Nothing (Left (map pNtoName pns')) imp
    inImport x = mzero

--same name but with different meaning is used.
causeAmbiguity pns mod
   = fromMaybe False (applyTU (once_tdTU (failTU `adhocTU` worker)) (hsDecls mod))
        where
         worker (pnt::PNT)
           | not (isQualifiedPN (pNTtoPN pnt)) && elem (pNTtoName pnt) (map pNtoName pns)
             && not (elem (pNTtoPN pnt) pns)
          = Just True
         worker _ = Nothing

resolveAmbiguity pns inScopeRel t
  =applyTP (full_tdTP (adhocTP idTP rename)) t
       where
         rename  pnt@(PNT pn@(PN (UnQual s) l) ty loc@(N (Just (SrcLoc fileName _  row col))))
          | isTopLevelPNT pnt && ty==Value && elem (pNTtoName pnt) (map pNtoName pns) && not (elem (pNTtoPN pnt) pns)
          = do let qual@(PlainModule q)= ghead "resolveAmbiguity" (hsQualifier pnt inScopeRel)
                   pnt'=(PNT (PN (Qual qual s) l) ty loc)
               update pnt pnt' pnt
         rename x = return x

-- getQualifier :: HsName.ModuleName->HsModuleP->HsName.ModuleName
getQualifier  modName (HsModule  _ _  _ imp _)
    = let r=(nub.ghead "getQualifier") (applyTU (once_tdTU (constTU [] `adhocTU` inImport)) imp)
      in if r==[] then modName
                  else head r
    where
    inImport ((HsImportDecl _ (SN m loc) _ as _ )::HsImportDeclP)
      | show modName == show m
      = if isJust as then return [simpModName (gfromJust "getQualifier"  as)]
                     else return []
    inImport _ = mzero

    -- simpModName :: PosSyntax.ModuleName ->HsName.ModuleName
    simpModName (SN m loc) = m

replaceQualifier pns qual  t
    =applyTP (full_tdTP (adhocTP idTP rename)) t
       where
         rename  pnt@(PNT pn ty loc)
          |isQualifiedPN pn && elem pn pns
          = do let pnt'=PNT (replaceQual pn qual) ty loc
               update pnt pnt' pnt
             where
              replaceQual (PN (Qual modName  s) l) qual = PN (Qual qual s) l
              replaceQual pn _ = pn
         rename x=return x

addQualifier pns qualifier t
  =applyTP (full_tdTP (adhocTP idTP rename)) t
       where
         rename pnt@(PNT pn@(PN (UnQual s) l) ty loc)
          | elem pn pns && isUsedInRhs pnt t
          = do let pnt'=(PNT (PN (Qual (strToModName qualifier) s) l) ty loc)
               update pnt pnt' pnt
         rename x=return x
