

module RefacRmDef(removeDef) where

import PosSyntax
import Data.Maybe
import TypedIds
import UniqueNames
import Data.List 
import TiPNT 
import RefacUtils 
import PNT

{-This refactoring removes a user selected function binding or a pattern binding if it is not used elsewhere
  When a function/pattern is removed, it's corresponding type signature should be removed as well. In the case
  that the type signature is like this a,b:: blah balh, only the name is removed from the type signature.
  A function binding  can be removed if the function name is not used elsewhere; A pattern binding can be 
  removed only if none of the names defined in this pattern binding is used elsewhere.
-}

removeDef args
 = do let fileName = ghead "filename" args 
          --fileName'= moduleName fileName
          --modName  = Module fileName'  
          row      = read (args!!1)::Int
          col      = read (args!!2)::Int
      (inscps, _, mod, tokList)<-parseSourceFile fileName         
      let pn = pNTtoPN $ locToPNT fileName (row, col) mod                                            
      if (pn /= defaultPN) 
       then if isTopLevelPN pn  
             then do let pns=pnsToBeRemoved pn mod 
                     if any (flip isExplicitlyExported mod) pns
                       then error "This definition can not be removed, as it is explicitly exported by this module!"
                       else do 
                               (mod',((tokList',modified),_))<-doRemoving pn fileName mod tokList
                               if isTopLevelPN pn 
                                then do modName <- RefacUtils.fileNameToModName fileName  
                                        clients<-clientModsAndFiles modName
                                        refactoredClients <- mapM (refactorInClientMod pns) clients
                                        writeRefactoredFiles False $ ((fileName,modified),(tokList',mod')):refactoredClients
                                else writeRefactoredFiles False [((fileName,modified), (tokList',mod'))]
             else do (mod',((tokList',modified),_))<-doRemoving pn fileName mod tokList
                     writeRefactoredFiles False [((fileName,modified), (tokList',mod'))]
       else error "\nInvalid cursor position!" 

doRemoving pn fileName mod tokList 
    =  runStateT (applyTP ((once_tdTP (failTP `adhocTP` rmInMod
                                              `adhocTP` rmInMatch
                                              `adhocTP` rmInPat
                                              `adhocTP` rmInLet
                                              `adhocTP` rmInAlt
                                              `adhocTP` rmInLetStmt)) `choiceTP` failure) mod)
                                                         ((tokList,unmodified),fileName)
                       
           where          
             --1. The definition to be removed is one of the module's top level declarations.
             rmInMod (mod@(HsModule loc name exps imps ds):: HsModuleP)  
                | canBeRemoved pn mod   
                  =do ds'<-rmDecl pn True ds
                      return (HsModule loc name exps imps ds') 
             rmInMod _ =mzero

             --2. The definition to be removed is a local declaration in a match
             rmInMatch (match@(HsMatch loc name pats rhs ds)::HsMatchP)
                 | canBeRemoved pn match
                   =do ds'<-rmDecl pn True ds
                       return (HsMatch loc name pats rhs ds')
             rmInMatch _ =mzero

             --3. The definition to be removed is a local declaration in a pattern binding
             rmInPat (pat@(Dec (HsPatBind loc p rhs ds))::HsDeclP)
                | canBeRemoved pn pat
                   =do ds'<- rmDecl pn True ds
                       return (Dec (HsPatBind  loc p rhs ds'))                      
             rmInPat _=mzero
              
             --4.The definition to be removed is a local declaration in a let expression
             rmInLet (letExp@(Exp (HsLet ds e))::HsExpP)
               | canBeRemoved pn letExp
                  =do ds'<- rmDecl pn True ds
                      if ds'==[] then return e
                                 else return (Exp (HsLet ds' e))
             rmInLet (letExp@(Exp (HsListComp (HsLetStmt ds stmts))))  -- e.g. [0|z=1] => [0]
               | canBeRemoved pn letExp
                 =do ds'<- rmDecl pn True ds 
                     if ds'/=[] 
                         then return (Exp (HsListComp (HsLetStmt ds' stmts)))
                         else if isLast stmts
                                then return (Exp (HsList [fromJust (expInLast stmts)]))
                                else return (Exp (HsListComp stmts))
             rmInLet _=mzero 
       
             --5. The defintion to be removed is a local decl in a case alternative.
             rmInAlt (alt@(HsAlt loc p rhs ds)::(HsAlt (HsExpP) (HsPatP) [HsDeclP]))
                |canBeRemoved pn alt
                =do ds'<- rmDecl pn True ds
                    return (HsAlt loc p rhs ds')
             rmInAlt _=mzero
            
             --6. The definition to be removed is a local decl in a let statement.
             rmInLetStmt (letStmt@(HsLetStmt ds stmts)::(HsStmt (HsExpP) (HsPatP) [HsDeclP]))
                |canBeRemoved pn letStmt
               =do ds'<- rmDecl pn True ds 
                   if ds'==[]  then return stmts
                              else return (HsLetStmt ds' stmts)
             rmInLetStmt _=mzero
      
             isLast (HsLast e)=True
             isLast _=False

             --returns the expression included in the last statement.
             expInLast::HsStmtP->Maybe HsExpP 
             expInLast (HsLast e)=Just e
             expInLast _=Nothing
 
             failure=idTP `adhocTP` mod
              where
               mod (m::HsModuleP)
                = error ("Refactoring Failed! Possible reasons: a) selected identifier is not a function/pattern name defined in this module;"++
                          " b) the identifer is used elsewhere;") 
  
             canBeRemoved pn t 
               =let decls=hsDecls t
                    decl=definingDecls1 [pn] decls False
                    pnames=concatMap definedPNs decl                    
                in (decl/=[] && all (not.flip findPN (replaceDecls t (decls \\ decl))) pnames)

  
pnsToBeRemoved pn t
 = let decls=hsDecls t
       decl=definingDecls [pn] decls False False
   in concatMap definedPNs decl         

refactorInClientMod pns (modName, fileName)
  = do (inscps, exps, mod ,ts) <-parseSourceFile fileName
       if any (flip findPN (hsModDecls mod)) pns || any (flip findPN (hsModExports mod)) pns
          then error $ "This definition can not be removed, as it is used by the client module '"++modName'++"'!"
          else do let pnsToBeHided= filter (flip findPN (hsModImports mod)) pns 
                  if pnsToBeHided/=[]  
                     then do (mod', ((ts',m),_))<-runStateT (rmItemsFromImport mod pnsToBeHided)
                                                       ((ts,unmodified),fileName)
                             return ((fileName,m), (ts',mod'))
                     else return ((fileName,unmodified), (ts,mod)) 
     where modName' = modNameToStr modName

--Find those declarations(function/pattern binding and type signature) which define pn-
--splitTypeSig indicates whether the corresponding type signature will be splited.
definingDecls1::[PName]->[HsDeclP]->Bool->[HsDeclP]
definingDecls1 pns ds incTypeSig=concatMap (defines pns) ds 
      where 
       defines pn decl@(Dec (HsFunBind loc ((HsMatch loc1 (PNT pname ty loc2) pats rhs ds):ms)))
          | isJust (find (==pname) pns)=[decl]
       defines pn decl@(Dec (HsPatBind loc p rhs ds))    ---CONSIDER AGAIN----
          |(hsPNs p) `intersect` pns /=[]=[decl]
       defines pn decl@(Dec (HsTypeSig loc is c tp)) --handle cases like  a,b::Int 
          |(map pNTtoPN is) `intersect` pns /=[]
          =if incTypeSig then [(Dec (HsTypeSig loc (filter (\x->isJust (find (==pNTtoPN x) pns)) is) c tp))]
                           else [decl]
       defines pn decl=[]   



