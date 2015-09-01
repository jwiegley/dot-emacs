

module RefacDupDef(duplicateDef {-,duplicateDef1-}) where

import PrettyPrint
import PosSyntax
import Data.Maybe
import TypedIds
import Data.List 
import TiPNT 
import RefacUtils 
import SourceNames
import HsName
import Prelude hiding (putStrLn)
import AbstractIO (putStrLn)

{-This refactoring duplicates a defintion(function binding or simple pattern binding) at same level with a new name
  provided by the user. The new name should not cause name clash/capture. 
-}
{-
----Begin: for experimenting interfaces------------------------
duplicateDef1 args
 = do let fileName     = ghead "filename" args 
          funNamePath  = args!!1
          newName      = args!!2
      if isVarId newName
       then do modName <-fileNameToModName fileName
               (inscps, _, mod, tokList) <-parseSourceFile fileName    
               case findPNameByPath funNamePath mod of 
                  Left errMsg -> putStrLn errMsg
                  Right pn  ->
                     do (mod',((tokList',m),_))<- doDuplicating pn newName (inscps, mod, tokList)
                        if modIsExported mod
                          then do clients <- clientModsAndFiles modName
                                  refactoredClients <-mapM (refactorInClientMod modName (findNewPName newName mod')) clients
                                  writeRefactoredFiles False $ ((fileName,m),(tokList',mod')):refactoredClients 
                          else  writeRefactoredFiles False [((fileName,m), (tokList',mod'))]
       else putStrLn "Invalid new function name!"    -}
-----End: for experimenting interfaces---------------------------------  

duplicateDef args
 = do let fileName = ghead "filename" args 
          newName  = args!!1 
          row      = read (args!!2)::Int
          col      = read (args!!3)::Int
      if isVarId newName 
        then do modName <-fileNameToModName fileName
                (inscps, _, mod, tokList) <-parseSourceFile fileName    
                let pn = pNTtoPN $ locToPNT fileName (row, col) mod                                            
                if (pn /= defaultPN) 
                  then do (mod',((tokList',m),_))<- doDuplicating pn newName (inscps, mod, tokList)
                          if modIsExported mod
                           then do clients <- clientModsAndFiles modName
                                   refactoredClients <- mapM (refactorInClientMod modName 
                                                              (findNewPName newName mod')) clients
                                   writeRefactoredFiles False $ ((fileName,m),(tokList',mod')):refactoredClients 
                           else  writeRefactoredFiles False [((fileName,m), (tokList',mod'))]
                  else error "Invalid cursor position!" 
        else error "Invalid new function name!"   
   
doDuplicating pn newName (inscps, mod, tokList)
   = runStateT (applyTP ((once_tdTP (failTP `adhocTP` dupInMod
                                            `adhocTP` dupInMatch
                                            `adhocTP` dupInPat
                                            `adhocTP` dupInLet
                                            `adhocTP` dupInAlt
                                            `adhocTP` dupInLetStmt)) `choiceTP` failure) mod)
                                     ((tokList,unmodified), (-1000))  -- the (-1000) should be deleted.
        where          
        --1. The definition to be duplicated is at top level.
        dupInMod (mod@(HsModule loc name exps imps ds):: HsModuleP)   
          |findFunOrPatBind  pn ds/=[]=doDuplicating' inscps mod pn  
        dupInMod _ =mzero

        --2. The definition to be duplicated is a local declaration in a match
        dupInMatch (match@(HsMatch loc1 name pats rhs ds)::HsMatchP)
          |findFunOrPatBind pn ds/=[]=doDuplicating' inscps match pn                                                    
        dupInMatch _ =mzero

        --3. The definition to be duplicated is a local declaration in a pattern binding
        dupInPat (pat@(Dec (HsPatBind loc p rhs ds))::HsDeclP)
          |findFunOrPatBind pn ds/=[]=doDuplicating' inscps pat pn                    
        dupInPat _=mzero
  
        --4: The defintion to be duplicated is a local decl in a Let expression
        dupInLet (letExp@(Exp (HsLet ds e))::HsExpP)
          |findFunOrPatBind pn  ds/=[]=doDuplicating' inscps letExp pn 
        dupInLet _=mzero
                
        --5. The defintion to be duplicated is a local decl in a case alternative.
        dupInAlt (alt@(HsAlt loc p rhs ds)::(HsAlt (HsExpP) (HsPatP) [HsDeclP]))
          |findFunOrPatBind pn ds/=[]=doDuplicating'  inscps alt pn 
        dupInAlt _=mzero
      
        --6.The definition to be duplicated is a local decl in a Let statement.
        dupInLetStmt (letStmt@(HsLetStmt ds stmts):: (HsStmt (HsExpP) (HsPatP) [HsDeclP]))
           |findFunOrPatBind pn  ds /=[]=doDuplicating' inscps letStmt pn 
        dupInLetStmt _=mzero

        
        failure=idTP `adhocTP` mod
          where
            mod (m::HsModuleP)
              = error "The selected identifier is not a function/simple pattern name, or is not defined in this module "
 
        findFunOrPatBind pn ds = filter (\d->isFunBind d || isSimplePatBind d) $ definingDecls [pn] ds True False

        doDuplicating' inscps parent pn 
           = do let decls           = hsDecls parent  
                    duplicatedDecls = definingDecls [pn] decls True False
                    (after,before)  = break (defines pn) (reverse decls)
                (f,d) <- hsFDNamesFromInside parent  
                 --f: names that might be shadowd by the new name, d: names that might clash with the new name
                dv <- hsVisibleNames pn decls --dv: names may shadow new name
                let inscpsNames = map ( \(x,_,_,_)-> x) $ inScopeInfo inscps
                    vars        = nub (f `union` d `union` dv)
                -- error ("RefacDupDef.doDuplicating' ...(f,d,inscpsNames,vars)=" ++ (show (f,d,inscpsNames,vars))) -- ++AZ++
                -- TODO: Where definition is of form tup@(h,t), test each element of it for clashes, or disallow    
                if elem newName vars || (isInScopeAndUnqualified newName inscps && findEntity pn duplicatedDecls) 
                   then error ("The new name'"++newName++"' will cause name clash/capture or ambiguity problem after "
                               ++ "duplicating, please select another name!")
                   else do newBinding<-duplicateDecl decls pn newName                            
                           return (replaceDecls parent (reverse before++ newBinding++ reverse after)) 
   


--Find the the new definition name in PName format. 
findNewPName name 
  =(fromMaybe defaultPN). applyTU (once_buTU (failTU `adhocTU` worker))
     where 
        worker  pname 
           |pNtoName pname == name = Just pname
        worker _ =mzero

                   
--Do refactoring in the client module.
-- that is to hide the identifer in the import declaration if it will cause any problem in the client module.
refactorInClientMod serverModName newPName (modName, fileName)
  = do (inscps, exps,mod ,ts) <- parseSourceFile fileName
       let modNames = willBeUnQualImportedBy serverModName mod   
       if isJust modNames && needToBeHided (pNtoName newPName) exps mod
        then do (mod', ((ts',m),_))<-runStateT (addHiding serverModName mod [newPName]) ((ts,unmodified),fileName)
                return ((fileName,m), (ts',mod')) 
        else return ((fileName,unmodified),(ts,mod))
   where
     needToBeHided name exps mod
         =usedWithoutQual name (hsModDecls mod)
          || causeNameClashInExports newPName name mod exps

--Check here:
--get the module name or alias name by which the duplicated definition will be imported automatically.
willBeUnQualImportedBy::HsName.ModuleName->HsModuleP->Maybe [HsName.ModuleName]
willBeUnQualImportedBy modName mod
   = let imps = hsModImports mod
         ms   = filter (\(HsImportDecl _ (SN modName1 _) qualify  as h)->modName==modName1 && (not qualify) && 
                          (isNothing h || (isJust h && ((fst (fromJust h))==True)))) imps
         in if ms==[] then Nothing
                      else Just $ nub $ map getModName ms

         where getModName (HsImportDecl _ (SN modName _) qualify  as h)
                 = if isJust as then simpModName (fromJust as)
                                else modName
               simpModName (SN m loc) = m
