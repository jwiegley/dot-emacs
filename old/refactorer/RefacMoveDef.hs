

module RefacMoveDef(liftToTopLevel, liftOneLevel, demote,liftingInClientMod) where
import Prelude hiding (putStrLn)
import PrettyPrint
import Data.Maybe
import Data.List 
import RefacUtils
import HsName
import AbstractIO

data Direction = UptoTopLevel | UpOneLevel | Down

{--------This function handles refactorings involving moving a defintion--------
 According to the Haskell's  syntax, a declaration may occur in one of the following six contexts:
  1. A top level declaration in the module:
            HsModule SrcLoc ModuleName (Maybe [HsExportSpecI i]) [HsImportDeclI i] ds
  2. A local declaration in a Match:
            HsMatch SrcLoc i [p] (HsRhs e) ds
  3. A local declaration in a pattern binding:
            HsPatBind SrcLoc p (HsRhs e) ds
  4. A local declaration in a Let expression:
            HsLet ds e
  5. A local declaration in a Case alternative:
            HsAlt SrcLoc p (HsRhs e) ds
  6. A local declaration in a Do statement:
            HsLetStmt ds (HsStmt e p ds)           
-}

liftToTopLevel args
 = do let  fileName = ghead "filename"  args 
           row = read (args!!1)::Int
           col = read (args!!2)::Int
      -- f <-  MT.lift $ getCurrentDirectory 
      modName <- fileNameToModName fileName 
      (inscps, _, mod, toks) <- parseSourceFile fileName  
      let pnt = locToPNT fileName (row, col) mod                                         
          pn = pNTtoPN pnt
      if pn /= defaultPN
         then liftToTopLevel' modName fileName (inscps, mod, toks) pnt
         else error "\nInvalid cursor position!\n"

liftOneLevel args
 = do let  fileName = ghead "filename"  args 
           row = read (args!!1)::Int
           col = read (args!!2)::Int
      modName <- fileNameToModName fileName 
      (inscps, _, mod, toks) <- parseSourceFile fileName  
      let pnt = locToPNT fileName (row, col) mod                                         
          pn = pNTtoPN pnt
      if pn /= defaultPN
         then liftOneLevel' modName fileName (inscps, mod, toks) pnt
         else error "\nInvalid cursor position!\n"


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
   This refactoring lifts a local function/pattern binding to the top level of the module, so as to 
    make it accessible to  other functions in the current module, and those modules that import 
    current module.  
    
   In the current implementation, a definition will be lifted only if none of the identifiers defined in this
   definition will cause name clash/capture problems in the current module after lifting. 

   In the case that the whole current module is exported implicitly, the lifted identifier will be  exported
   automatically after lifting. If the identifier will cause name clash/ambiguous occurrence problem in a 
   client module, it will be hided in the import declaration of the client module (Note: this might not be 
   the best solution, we prefer hiding it in the server module instead of in the client module in the final version).

   In the case of indirect importing, it might be time-consuming to trace whether the lifted identifier
   will cause any problem in a client module that indirectly imports the current  module. The current solution is:
   suppose a defintion is lifted to top level in module A, and module A is imported and exported by module B, then
   the lifted identifier will be hided in the import declaration of B no matter whether it causes problems in 
   module B or not.  
 
   Function name: liftToTopLevel 
   parameters: fileName--current file name. 
               mod -- the scoped abstract syntax tree of the module.
               pn  -- the function/pattern name to be lifted.        
-}

liftToTopLevel' modName fileName (inscps, mod, toks) pnt@(PNT pn _ _)   
  = if isLocalFunOrPatName pn mod     
      then do ((mod',declPns),((toks',m),_))<-runStateT liftToMod ((toks,unmodified),(-1000,0))            
              if modIsExported mod  
               then do clients<-clientModsAndFiles modName  
                       refactoredClients <- mapM (liftingInClientMod modName declPns) clients
                       writeRefactoredFiles False $ ((fileName,m),(toks',mod')):refactoredClients                          
               else do writeRefactoredFiles False [((fileName,m), (toks',mod'))]
      else error "\nThe identifier is not a local function/pattern name!" 
   
     where 
          {-step1: divide the module's top level declaration list into three parts:
            'parant' is the top level declaration containing the lifted declaration,
            'before' and `after` are those declarations before and after 'parent'.
            step2: get the declarations to be lifted from parent, bind it to liftedDecls 
            step3: remove the lifted declarations from parent and extra arguments may be introduce.
            step4. test whether there are any names need to be renamed. 
          -}       
       liftToMod = do let (before, parent,after)=divideDecls (hsDecls mod) pnt                               
                      when (isClassDecl $ ghead "liftToMod" parent) 
                            $ error "Sorry, the refactorer cannot lift a definition from a class declaration!"
                      when (isInstDecl $ ghead "liftToMod" parent)
                            $ error "Sorry, the refactorer cannot lift a definition from an instance declaration!"
                      let liftedDecls=definingDecls [pn] parent True True
                          declaredPns=nub $ concatMap definedPNs liftedDecls                                         
                      pns<-pnsNeedRenaming inscps mod parent liftedDecls declaredPns
                      (_,dd)<-hsFreeAndDeclaredPNs mod
                      if pns==[] 
                        then do (parent',liftedDecls',paramAdded)<-addParamsToParentAndLiftedDecl pn dd parent liftedDecls
                                let liftedDecls''=if paramAdded then filter isFunOrPatBind liftedDecls'
                                                                else liftedDecls'
                                mod'<-moveDecl1 (replaceDecls mod (before++parent'++after))
                                       (Just (ghead "liftToMod" (definedPNs (ghead "liftToMod2" parent')))) [pn] True
                                return (mod', declaredPns) 
                        else askRenamingMsg pns "lifting"


moveDecl1 t defName pns topLevel
   = do ((toks, _),_)<-get
        let (declToMove, toksToMove) = getDeclAndToks (ghead "moveDecl1" pns) True toks t
	--error$ show (declToMove, toksToMove)
        t' <- rmDecl (ghead "moveDecl3"  pns) False =<<foldM (flip rmTypeSig) t pns
        addDecl t' defName (declToMove, Just toksToMove) topLevel
         

--get all the declarations define in the scope of t
allDeclsIn t = fromMaybe [] (applyTU (full_tdTU (constTU [] `adhocTU` decl)) t)               
               where decl (d::HsDeclP)
                       |isFunBind d || isPatBind d || isTypeSig d = Just [d]
                     decl _ = Just [] 

askRenamingMsg pns str 
  = error ("The identifier(s):" ++ showEntities showPNwithLoc pns ++
           " will cause name clash/capture or ambiguity occurrence problem after "
           ++ str ++", please do renaming first!")             

--Get the subset of 'pns' that need to be renamed before lifting.
pnsNeedRenaming inscps dest parent liftedDecls pns
   =do r<-mapM pnsNeedRenaming' pns   
       return (concat r)
  where                 
     pnsNeedRenaming' pn
       = do (f,d)<-hsFDsFromInside dest  --f: free variable names that may be shadowed by pn
                                             --d: declaread variables names that may clash with pn
            vs<-hsVisiblePNs pn parent      --vs: declarad varaibles that may shadow pn          
            let inscpNames = map (\(x,_,_,_)->x) $ inScopeInfo inscps
                vars = map pNtoName (nub (f `union` d `union` vs) \\ [pn]) -- `union` inscpNames            
            if elem (pNtoName pn) vars  || isInScopeAndUnqualified (pNtoName pn) inscps && findEntity pn dest 
               then return [pn]
               else return []
     --This pNtoName takes into account the qualifier.
     pNtoName (PN (UnQual i) orig)=i    
     pNtoName (PN (Qual (PlainModule modName) i ) orig)=modName ++ "." ++ i        
 
--can not simply use PNameToExp, PNameToPat here because of the location information. 
addParamsToParent pn [] t = return t
addParamsToParent pn params t
   =applyTP(full_buTP (idTP  `adhocTP` inExp)) t 
   where              
          inExp (exp@(Exp (HsId (HsVar (PNT pname ty loc))))::HsExpP)
            | pname==pn
             = do  let newExp=Exp (HsParen (foldl addParamToExp exp (map pNtoExp params)))
                   update exp newExp exp

          inExp x =return x                   
   
          addParamToExp  exp param
              =(Exp (HsApp exp param))  

--Do refactoring in the client module.
-- that is to hide the identifer in the import declaration if it will cause any problem in the client module.

liftingInClientMod serverModName pns (modName, fileName)
  = do (inscps, exps ,mod ,ts) <- parseSourceFile fileName
       let modNames = willBeUnQualImportedBy serverModName mod   
       if isJust modNames
        then let pns' = namesNeedToBeHided mod exps (fromJust modNames) pns
             in if pns' /= [] 
                 then do (mod', ((ts',m),_))<-runStateT (addHiding serverModName mod pns') ((ts,unmodified),(-1000,0))
                         return ((fileName,m), (ts',mod')) 
                 else return ((fileName,unmodified), (ts,mod))
        else return ((fileName,unmodified),(ts,mod))


--Test whether an identifier defined in the modules specified by 'names' will be exported by current module.
willBeExportedByClientMod names mod
  = let exps = hsModExports mod
    in if isNothing exps 
          then False
          else any isJust $ map (\y-> (find (\x-> (simpModule x==Just y)) (fromJust exps))) names
      where simpModule (ModuleE (SN m _)) = Just m
            simpModule _  = Nothing 

--get the module name or alias name by which the lifted identifier will be imported automatically.
willBeUnQualImportedBy::HsName.ModuleName->HsModuleP->Maybe [HsName.ModuleName]
willBeUnQualImportedBy modName mod
   = let imps  = hsModImports mod
         ms =filter (\(HsImportDecl _ (SN modName1 _) qualify  as h)->modName==modName1 && (not qualify) && 
                          (isNothing h || (isJust h && ((fst (fromJust h))==True)))) imps
         in if ms==[] then Nothing
                      else Just $ nub $ map getModName ms

         where getModName (HsImportDecl _ (SN modName _) qualify  as h)
                 = if isJust as then simpModName (fromJust as)
                                else modName
               simpModName (SN m loc) = m

--get the subset of 'pns', which need to be hided in the import declaration in module 'mod'
namesNeedToBeHided mod exps modNames  pns
  = if willBeExportedByClientMod modNames mod
      then pns 
      else concatMap needToBeHided pns
    where
      needToBeHided  pn 
        = let name = pNtoName pn 
          in if (usedWithoutQual name (hsModDecls mod) --the same name is used in the module unqualifiedly
                || usedWithoutQual name (hsModExports mod)  --the same name is exported unqualifiedly by an Ent decl
                || causeNameClashInExports pn name mod exps)
              then [pn] 
              else []


-- **************************************************************************************************************--

{- Refactoring Names: 'liftOneLevel'
   Descritption:
    this refactoring lifts a local function/pattern binding only one level up. 
    By 'lifting one-level up' ,I mean: 
    case1: In a module (HsModule SrcLoc ModuleName (Maybe [HsExportSpecI i]) [HsImportDeclI i] ds):
           A local declaration D  will be lifted to the same level as the 'ds', if D is in the 
           where clause of one of ds's element declaration.

    case2: In a match ( HsMatch SrcLoc i [p] (HsRhs e) ds) :
          A local declaration D  will be lifted to the same level as the 'ds', if D is in the 
           where clause of one of ds's element declaration.
           A declaration D,say,in the rhs expression 'e' will be lifted to 'ds' if D is Not local to
           other declaration list in 'e'

    case3: In a pattern  binding (HsPatBind SrcLoc p (HsRhs e) ds):
           A local declaration D  will be lifted to the same level as the 'ds', if D is in the 
           where clause of one of ds's element declaration.
           A declaration D,say,in the rhs expression 'e' will be lifted to 'ds' if D is Not local to
           other declaration list in 'e'

    case4: In the Lex expression (Exp (HsLet ds e):
           A local declaration D  will be lifted to the same level as the 'ds', if D is in the 
           where clause of one of ds's element declaration.
           A declaration D, say, in the expression 'e' will be lifted to 'ds' if D is not local to
           other declaration list in 'e'
    case5: In the case Alternative expression:(HsAlt loc p rhs ds)
           A local declaration D  will be lifted to the same level as the 'ds', if D is in the 
           where clause of one of ds's element declaration.
           A declaration D in 'rhs' will be lifted to 'ds' if D is not local to other declaration 
           list in 'rhs'.

    case6: In the do statement expression:(HsLetStmt ds stmts)
           A local declaration D  will be lifted to the same level as the 'ds', if D is in the 
           where clause of one of ds's element declaration.
           A declaration D in 'stmts' will be lifted to 'ds' if D is not local to other declaration 
           list in 'stmts'.           
    
Function name: liftOneLevel 
parameters: fileName--current file name.
            mod -- the scoped abstract syntax tree of the module.
            pn  -- the function/pattern name to be lifted.
       
-}

liftOneLevel' modName fileName (inscps, mod, toks) pnt@(PNT pn _ _ )   
   = if isLocalFunOrPatName pn mod
        then do (mod', ((toks',m),_))<-liftOneLevel''            
                let (b, pns) = liftedToTopLevel pnt mod
                if b &&  modIsExported mod  
                  then do clients<-clientModsAndFiles modName 
                          refactoredClients <- mapM (liftingInClientMod modName pns) clients
                          -- ePutStrLn (show clients)
                          writeRefactoredFiles False $ ((fileName,m),(toks',mod')):refactoredClients     
                  else writeRefactoredFiles False [((fileName,m), (toks',mod'))]
        else error "\nThe identifer is not a function/pattern name!"

   where
      liftOneLevel''=runStateT (applyTP ((once_tdTP (failTP `adhocTP` liftToMod
                                                            `adhocTP` liftToMatch
                                                            `adhocTP` liftToPattern 
                                                            `adhocTP` liftToLet
                                                             `adhocTP` liftToAlt
                                                            `adhocTP` liftToLetStmt))
                                          `choiceTP` failure) mod) ((toks,unmodified),(-1000,0))
           where          
             --1. The defintion will be lifted to top level
             liftToMod (mod@(HsModule loc name exps imps ds):: HsModuleP)   
                | definingDecls [pn] (hsDecls ds) False False /=[]  --False means not taking type signature into account 
                  =do ds'<-worker mod ds pn 
                      return (HsModule loc name exps imps ds')
             liftToMod  _ =mzero
         
             --2. The definition will be lifted to the declaration list of a match
             liftToMatch (match@(HsMatch loc1 name pats rhs ds)::HsMatchP)
                 | definingDecls [pn] (hsDecls ds) False False/=[] 
                  =do ds'<-worker match ds pn            
                      return (HsMatch loc1 name pats rhs ds')

             liftToMatch (match@(HsMatch loc1 name pats rhs ds)::HsMatchP)
                 | definingDecls [pn] (hsDecls rhs) False False /=[] 
                  = doLifting1 match pn    
             liftToMatch _ =mzero

             --3. The definition will be lifted to the declaration list of a pattern binding 
             liftToPattern (pat@(Dec (HsPatBind loc p rhs ds))::HsDeclP)
                | definingDecls [pn] (hsDecls ds) False  False /=[] 
                  =do ds'<-worker pat ds pn 
                      return (Dec (HsPatBind loc p rhs ds'))

             liftToPattern (pat@(Dec (HsPatBind loc p rhs ds))::HsDeclP)
                | definingDecls [pn] (hsDecls rhs) False  False /=[] 
                  =doLifting2 pat  pn 
             liftToPattern _=mzero

             --4. The definition will be lifted to the declaration list in a let expresiion.
             liftToLet (letExp@(Exp (HsLet ds e))::HsExpP)
               | definingDecls [pn] (hsDecls ds) False  False/=[] 
                =do ds' <-worker letExp ds pn  
                    return (Exp (HsLet ds' e))

             liftToLet (letExp@(Exp (HsLet ds e))::HsExpP)  --Attention: ds can be empty!
               | definingDecls [pn] (hsDecls e) False  False /=[] 
                = doLifting3 letExp pn  
             liftToLet _ =mzero 
 
           
             --5. The definition will be lifted to the declaration list in a alt
             liftToAlt (alt@(HsAlt loc p rhs ds)::(HsAlt (HsExpP) (HsPatP) [HsDeclP]))
                |definingDecls [pn] (hsDecls ds) False  False /=[] 
                =do ds'<-worker alt ds pn 
                    return (HsAlt loc p rhs ds')

             liftToAlt (alt@(HsAlt loc p rhs ds)::(HsAlt (HsExpP) (HsPatP) [HsDeclP]))
                |definingDecls [pn] (hsDecls rhs) False  False/=[] 
                =doLifting4  alt  pn
             liftToAlt _=mzero

             --6. The defintion will be lifted to the declaration list in a let statement.
             liftToLetStmt (letStmt@(HsLetStmt ds stmts):: (HsStmt (HsExpP) (HsPatP) [HsDeclP]))
                |definingDecls [pn] (hsDecls ds) False  False/=[] 
               =do ds'<-worker letStmt ds pn  
                   return (HsLetStmt ds' stmts)
              
             liftToLetStmt (letStmt@(HsLetStmt ds stmts):: (HsStmt (HsExpP) (HsPatP) [HsDeclP])) 
                |definingDecls [pn] (hsDecls stmts) False False /=[] 
               = doLifting5 letStmt pn 
             liftToLetStmt _=mzero

             failure=idTP `adhocTP` mod
                where
                  mod (m::HsModuleP)
                   = error ( "Lifting this definition failed. "++
                           " This might be because that the definition to be lifted is defined in a class/instance declaration.")

             worker dest ds pn
                  =do let (before, parent,after)=divideDecls ds pnt                                    
                          liftedDecls=definingDecls [pn] (hsDecls parent) True  False
                          declaredPns=nub $ concatMap definedPNs liftedDecls
                      (_, dd)<-hsFreeAndDeclaredPNs dest 
                      pns<-pnsNeedRenaming inscps dest parent liftedDecls declaredPns
                      if pns==[]
                        then do 
                                (parent',liftedDecls',paramAdded)<-addParamsToParentAndLiftedDecl pn dd
                                                                     parent liftedDecls 
                                let liftedDecls''=if paramAdded then filter isFunOrPatBind liftedDecls'
                                                                else liftedDecls'
                                --True means the new decl will be at the same level with its parant. 
                                dest'<-moveDecl1 (replaceDecls dest (before++parent'++after))
                                           (Just (ghead "liftToMod" (definedPNs (ghead "worker" parent')))) [pn] False
                                return (hsDecls dest')
                                --parent'<-doMoving declaredPns (ghead "worker" parent) True  paramAdded parent'
                                --return (before++parent'++liftedDecls''++after)
                        else askRenamingMsg pns "lifting"

             doLifting1 dest@(HsMatch loc1 name pats parent ds)  pn 
               = do  let  liftedDecls=definingDecls [pn] (hsDecls parent) True  False
                          declaredPns=nub $ concatMap definedPNs liftedDecls
                     pns<-pnsNeedRenaming inscps dest parent liftedDecls declaredPns
                     (_, dd)<-hsFreeAndDeclaredPNs dest 
                     if pns==[]
                       then do (parent',liftedDecls',paramAdded)<-addParamsToParentAndLiftedDecl pn dd parent liftedDecls
                               let liftedDecls''=if paramAdded then filter isFunOrPatBind liftedDecls'
                                                                else liftedDecls'
                               moveDecl1 (HsMatch loc1 name pats parent' ds) Nothing [pn] False 
                        else askRenamingMsg pns "lifting"
             doLifting2 dest@(Dec (HsPatBind loc p parent ds)) pn 
               = do  let  liftedDecls=definingDecls [pn] (hsDecls parent) True  False
                          declaredPns=nub $ concatMap definedPNs liftedDecls
                     pns<-pnsNeedRenaming inscps dest parent liftedDecls declaredPns
                     (_, dd)<-hsFreeAndDeclaredPNs dest 
                     if pns==[]
                       then do (parent',liftedDecls',paramAdded)<-addParamsToParentAndLiftedDecl pn dd parent liftedDecls
                               let liftedDecls''=if paramAdded then filter isFunOrPatBind liftedDecls'
                                                                else liftedDecls'
                               moveDecl1 (Dec (HsPatBind loc p parent' ds)) Nothing [pn] False 
                         else askRenamingMsg pns "lifting"
                                
             doLifting3 dest@(Exp (HsLet ds parent)) pn 
               = do  let  liftedDecls=definingDecls [pn] (hsDecls parent) True  False
                          declaredPns=nub $ concatMap definedPNs liftedDecls
                     pns<-pnsNeedRenaming inscps dest parent liftedDecls declaredPns
                     (_, dd)<-hsFreeAndDeclaredPNs dest 
                     if pns==[]
                       then do (parent',liftedDecls',paramAdded)<-addParamsToParentAndLiftedDecl pn dd parent liftedDecls
                               let liftedDecls''=if paramAdded then filter isFunOrPatBind liftedDecls'
                                                                else liftedDecls'
                               moveDecl1 (Exp (HsLet ds parent')) Nothing [pn] False 
                         else askRenamingMsg pns "lifting"

             doLifting4 dest@(HsAlt loc p parent ds) pn 
               = do  let  liftedDecls=definingDecls [pn] (hsDecls parent) True  False
                          declaredPns=nub $ concatMap definedPNs liftedDecls
                     pns<-pnsNeedRenaming inscps dest parent liftedDecls declaredPns
                     (_, dd)<-hsFreeAndDeclaredPNs dest 
                     if pns==[]
                       then do (parent',liftedDecls',paramAdded)<-addParamsToParentAndLiftedDecl pn dd parent liftedDecls
                               let liftedDecls''=if paramAdded then filter isFunOrPatBind liftedDecls'
                                                                else liftedDecls'
                               moveDecl1 (HsAlt loc p parent' ds) Nothing [pn] False 
                         else askRenamingMsg pns "lifting"
             doLifting5 dest@(HsLetStmt ds parent) pn 
               = do  let  liftedDecls=definingDecls [pn] (hsDecls parent) True  False
                          declaredPns=nub $ concatMap definedPNs liftedDecls
                     pns<-pnsNeedRenaming inscps dest parent liftedDecls declaredPns
                     (_, dd)<-hsFreeAndDeclaredPNs dest 
                     if pns==[]
                       then do (parent',liftedDecls',paramAdded)<-addParamsToParentAndLiftedDecl pn dd parent liftedDecls
                               let liftedDecls''=if paramAdded then filter isFunOrPatBind liftedDecls'
                                                                else liftedDecls'
                               moveDecl1 (HsLetStmt ds parent') Nothing [pn] False 
                         else askRenamingMsg pns "lifting"
                                 


liftedToTopLevel pnt@(PNT pn _ _) (mod@(HsModule loc name exps imps ds):: HsModuleP)  
  = if definingDecls [pn] (hsDecls ds) False True /=[] 
     then let (_, parent,_) = divideDecls ds pnt
              liftedDecls=definingDecls [pn] (hsDecls parent) True True                                 
              declaredPns  = nub $ concatMap definedPNs liftedDecls
          in (True, declaredPns)
     else (False, [])

addParamsToParentAndLiftedDecl pn dd parent liftedDecls
  =do  (ef,_)<-hsFreeAndDeclaredPNs parent
       (lf,_)<-hsFreeAndDeclaredPNs liftedDecls   
       let newParams=((nub lf)\\ (nub ef)) \\ dd  --parameters (in PName format) to be added to pn because of lifting
       if newParams/=[]  
         then if  (any isComplexPatBind liftedDecls)
                then error "This pattern binding cannot be lifted, as it uses some other local bindings!"
                else do parent'<-{-addParamsToDecls parent pn newParams True-} addParamsToParent pn newParams parent
                        liftedDecls'<-addParamsToDecls liftedDecls pn newParams True 
                        return (parent', liftedDecls',True)
         else return (parent,liftedDecls,False)

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

demote' modName fileName (mod,toks) pn
  =if isFunOrPatName pn mod 
    then if isTopLevelPN pn && isExplicitlyExported pn mod 
          then error "This definition can not be demoted, as it is explicitly exported by the current module!"
          else do (mod',((toks',m),_))<-doDemoting pn fileName mod toks
                  if isTopLevelPN pn && modIsExported mod  
                    then do let demotedDecls'= definingDecls [pn] (hsDecls mod) True False
                                declaredPns  = nub $ concatMap definedPNs demotedDecls'
                            clients<-clientModsAndFiles modName
                            refactoredClients <-mapM (demotingInClientMod declaredPns) clients
                            writeRefactoredFiles False $ ((fileName,m),(toks',mod')):refactoredClients     
                    else writeRefactoredFiles False [((fileName,m), (toks',mod'))]
    else error "\nInvalid cursor position!"


--Do refactoring in the client module, that is:
--a) Check whether the identifier is used in the module body
--b) If the identifier is not used but is hided by the import declaration, then remove it from the hiding.

demotingInClientMod pns (modName, fileName)
  = do (inscps, exps, mod ,ts) <- parseSourceFile fileName
       if any (\pn->findPN pn (hsModDecls mod) || findPN pn (hsModExports mod)) pns
          then error $ "This definition can not be demoted, as it is used in the client module '"++show modName++"'!"
          else if any (\pn->findPN pn (hsModImports mod)) pns 
                  then do (mod',((ts',m),_))<-runStateT (rmItemsFromImport mod pns) ((ts,unmodified),(-1000,0))
                          return ((fileName,m), (ts',mod'))
                  else return ((fileName,unmodified), (ts,mod)) 


doDemoting  pn fileName mod toks
 =runStateT (applyTP ((once_tdTP (failTP `adhocTP` demoteInMod
                                         `adhocTP` demoteInMatch 
                                         `adhocTP` demoteInPat
                                         `adhocTP` demoteInLet
                                         `adhocTP` demoteInAlt
                                         `adhocTP` demoteInStmt)) `choiceTP` failure) mod)
                     ((toks,unmodified),(-1000,0))
    where
       --1. demote from top level
       demoteInMod (mod@(HsModule loc name exps imps ds):: HsModuleP)  
         |definingDecls [pn] ds False False /=[] 
         = do mod'<-rmQualifier [pn] mod 
              doDemoting' mod' pn
       demoteInMod _ =mzero
       
        --2. The demoted definition is a local decl in a match  
       demoteInMatch (match@(HsMatch loc1 name pats rhs ds)::HsMatchP)
         | definingDecls [pn] ds False False/=[] 
         = doDemoting' match pn
       demoteInMatch  _ =mzero

       --3. The demoted definition is a local decl in a pattern binding
       demoteInPat (pat@(Dec (HsPatBind loc p rhs ds))::HsDeclP)
         | definingDecls [pn] ds False False /=[] 
          = doDemoting' pat pn           
       demoteInPat _ =mzero

       --4: The demoted definition is a local decl in a Let expression
       demoteInLet (letExp@(Exp (HsLet ds e))::HsExpP)
         | definingDecls [pn] ds False False/=[] 
          = doDemoting' letExp pn
       demoteInLet _=mzero
                
       --5. The demoted definition is a local decl in a case alternative.
       demoteInAlt (alt@(HsAlt loc p rhs ds)::(HsAlt (HsExpP) (HsPatP) [HsDeclP]))
         | definingDecls [pn] ds False False /=[] 
          = doDemoting'  alt pn
       demoteInAlt _=mzero
      
       --6.The demoted definition is a local decl in a Let statement.
       demoteInStmt (letStmt@(HsLetStmt ds stmts):: (HsStmt (HsExpP) (HsPatP) [HsDeclP]))
         | definingDecls [pn] ds False False /=[] 
          = doDemoting' letStmt pn
       demoteInStmt _=mzero

       failure=idTP `adhocTP` mod
             where
               mod (m::HsModuleP)
                = error "Refactoring failed!"   --SHOULD GIVE MORE DETAILED ERROR MESSAGE
     
{- doDemoting' :(MonadPlus m)=>PName->[HsDeclP]->m [HsDeclP] 
   parameters:  t -declaration or expression  where pn is define.
                pn -- the function/pattern name to be demoted in PName format    
            
-}
doDemoting' t pn 
 = let origDecls=hsDecls t
       demotedDecls'=definingDecls [pn] origDecls True False
       declaredPns=nub $ concatMap definedPNs demotedDecls'
       demotedDecls=definingDecls declaredPns origDecls True False
   in if not (usedByRhs t declaredPns)
       then do -- find how many matches/pattern bindings (except the binding defining pn) use 'pn' 
              uselist<-uses declaredPns (hsDecls t\\demotedDecls)
                      {- From 'hsDecls t' to 'hsDecls t \\ demotedDecls'. 
                         Bug fixed 06/09/2004 to handle direct recursive function.
                       -}
              case  length uselist  of
                  0 ->do error "\n Nowhere to demote this function!\n"
                  1 -> --This function is only used by one friend function 
                      do (f,d)<-hsFreeAndDeclaredPNs demotedDecls 
                          -- remove demoted declarations
                         --Without updating the token stream.
                         let ds=foldl (flip removeTypeSig) (hsDecls t\\demotedDecls) declaredPns  
                         --get those varaibles declared at where the demotedDecls will be demoted to
                         dl  <-mapM (flip declaredNamesInTargetPlace ds) declaredPns
                         --make sure free variable in 'f' do not clash with variables in 'dl', 
                         --otherwise do renaming. 
                         let clashedNames=filter (\x-> elem (pNtoName x) (map pNtoName f)) $ (nub.concat) dl
                         --rename clashed names to new names created automatically,update TOKEN STREAM as well.
                         if clashedNames/=[] 
                            then error ("The identifier(s):" ++ showEntities showPNwithLoc clashedNames ++
                                       ", declared in where the definition will be demoted to, will cause name clash/capture"
                                       ++" after demoting, please do renaming first!")  
                                 --ds'<-foldM (flip (autoRenameLocalVar True)) ds clashedNames
                            else  --duplicate demoted declarations to the right place.
                                 do ds''<-duplicateDecls declaredPns origDecls 
                                    return (replaceDecls t ds'')
                  _ ->error "\nThis function/pattern binding is used by more than one friend bindings\n"
                       
      else error "This function can not be demoted as it is used in current level!\n"            
    where
          ---find how many matches/pattern bindings use  'pn'------- 
          uses pns 
               = applyTU (stop_tdTU (failTU `adhocTU` usedInMatch
                                            `adhocTU` usedInPat))                           
                where
                  usedInMatch (match@(HsMatch _ (PNT pname _ _) _ _ _)::HsMatchP)
                     | isNothing (find (==pname) pns) && any  (flip findPN match) pns
                     =return ["Once"]
                  usedInMatch _ =mzero

                  usedInPat (pat@(Dec (HsPatBind _ p _ _)):: HsDeclP)
                    | hsPNs p `intersect` pns ==[]  && any  (flip findPN pat) pns
                    =return ["Once"]
                  usedInPat  _=mzero 

          -- duplicate demotedDecls to the right place (the outer most level where it is used).
          duplicateDecls  pns decls
             = do applyTP (once_tdTP (failTP `adhocTP` dupInMatch 
                                             `adhocTP` dupInPat)) decls
                  --error (show decls' ++ "\n" ++ prettyprint decls')
                  -- rmDecl (ghead "moveDecl3"  pns) False =<<foldM (flip rmTypeSig) decls' pns 
               where 
                 dupInMatch (match@(HsMatch loc1 name pats rhs ds)::HsMatchP)
                   | any (flip findPN match) pns && not (any (flip findPN name) pns)
                   =  --If not fold parameters. 
                      moveDecl pns match False decls False
                      -- If fold parameters.
                      --foldParams pns match decls 
                 dupInMatch _ =mzero
     
                 dupInPat (pat@(Dec (HsPatBind loc p rhs ds))::HsDeclP)
                    |any (flip findPN pat) pns && not (any (flip findPN p) pns)
                   =  moveDecl pns pat False decls False
                 dupInPat _ =mzero  
              
                 demotedDecls=definingDecls pns decls True False
          ---------------------------------------------------------------------
          declaredNamesInTargetPlace :: (Term t, MonadPlus m)=>PName->t->m [PName]
          declaredNamesInTargetPlace pn=applyTU (stop_tdTU (failTU 
                                                    `adhocTU` inMatch  
                                                    `adhocTU` inPat))                            
               where
                 inMatch (match@(HsMatch loc1 name pats rhs ds)::HsMatchP)
                    | findPN pn rhs
                     =(return.snd)=<<hsFDsFromInside match 
                 inMatch _ =mzero

                 inPat (pat@(Dec (HsPatBind loc p rhs ds)):: HsDeclP)
                    |findPN pn rhs
                     =(return.snd)=<<hsFDsFromInside pat 
                 inPat _=mzero  

class (Term t) =>UsedByRhs t where
  
    usedByRhs:: t->[PName]->Bool

instance UsedByRhs HsExpP where
    usedByRhs (Exp (HsLet ds e)) pns = or $ map (flip findPN e) pns

instance UsedByRhs HsAltP where
    usedByRhs (HsAlt _ _ rhs _) pns  =or $ map (flip findPN rhs) pns 

instance UsedByRhs HsStmtP where
    usedByRhs (HsLetStmt _ stmt) pns =or $ map (flip findPN stmt) pns  

instance UsedByRhs HsMatchP where   
    usedByRhs (HsMatch loc1 fun pats rhs ds) pns =or $ map (flip findPN rhs) pns   
           
instance UsedByRhs  HsDeclP where
    usedByRhs (Dec (HsPatBind loc p rhs ds)) pns =or $ map (flip findPN rhs) pns               
    usedByRhs _ pn=False

instance UsedByRhs HsModuleP where
    usedByRhs mod pns=False


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
--- TEST THIS FUCNTION!!!
foldParams pns (match@(HsMatch loc1 name pats rhs ds)::HsMatchP) decls  
     =do let matches=concatMap matchesInDecls demotedDecls
             pn=ghead "foldParams" pns    --pns /=[]
         params<-allParams pn rhs []
         if (length.nub.map length) params==1                  -- have same number of param 
             && ((length matches)==1)      -- only one 'match' in the demoted declaration             
           then do let patsInDemotedDecls=(patsInMatch.(ghead "foldParams")) matches
                       subst=mkSubst patsInDemotedDecls params
                       fstSubst=map fst subst
                       sndSubst=map snd subst
                   rhs'<-rmParamsInParent pn sndSubst rhs
                   ls<-mapM hsFreeAndDeclaredPNs sndSubst
                   -- newNames contains the newly introduced names to the demoted decls---
                   let newNames=(map pNtoName (concatMap fst ls)) \\ (map pNtoName fstSubst)
                   --There may be name clashing because of introducing new names.
                   clashedNames<-getClashedNames fstSubst newNames (ghead "foldParams" matches)
                  {- --auotmatic renaming 
                   demotedDecls'<-foldM (flip (autoRenameLocalVar True)) demotedDecls clashedNames
                   demotedDecls''<- foldM replaceExpWithUpdToks demotedDecls' subst 
                   --remove substituted parameters in demoted declarations
                   demotedDecls'''<-rmParamsInDemotedDecls fstSubst demotedDecls'' -}
                   decls' <- foldInDemotedDecls pns clashedNames subst decls
                   let demotedDecls''' = definingDecls pns decls' True False
                   moveDecl pns (HsMatch loc1 name pats rhs' ds) False decls' False                  
                   return (HsMatch loc1 name pats rhs' (ds++(filter (not.isTypeSig) demotedDecls''')))
           else  do  moveDecl pns match False decls True
                     return (HsMatch loc1 name pats rhs (ds++demotedDecls))  -- no parameter folding 

    where  

       matchesInDecls ((Dec (HsFunBind loc matches))::HsDeclP)=matches
       matchesInDecls x = []     
         
       patsInMatch ((HsMatch loc1 name pats rhs ds)::HsMatchP)
         =pats

       demotedDecls=definingDecls pns decls True False
           

       foldInDemotedDecls  pns clashedNames subst decls
          = applyTP (stop_tdTP (failTP `adhocTP` worker)) decls  
          where
          worker (match@(HsMatch loc1 (PNT pname _ _) pats rhs ds)::HsMatchP)
            | isJust (find (==pname) pns) 
            = do match' <- foldM (flip (autoRenameLocalVar True)) match clashedNames
                 match'' <- foldM replaceExpWithUpdToks match' subst
                 rmParamsInDemotedDecls (map fst subst) match''

          worker _ = mzero
                    

      ------Get all of the paramaters supplied to pn --------------------------- 
            {- eg. sumSquares x1 y1 x2 y2 = rt x1 y1 + rt x2 y2
                   rt x y = x+y
              demote 'rt' to 'sumSquares',
              'allParams pn rhs []'  returns [[x1,x2],[y1,y2]]
                where pn is 'rt' and  rhs is 'rt x1 y1 + rt x2 y2'             
           -}
       allParams pn rhs initial  -- pn: demoted function/pattern name.
        =do p<-getOneParam pn rhs
            --putStrLn (show p)
            if p/=[] then do rhs'<-rmOneParam pn rhs
                             allParams pn rhs' (initial++[p])           
                     else return initial
        where
           getOneParam pn 
              =applyTU (stop_tdTU (failTU `adhocTU` worker))
                where
                  worker (Exp (HsApp e1 e2))
                   |(expToPN e1==pn) =return (rmLocs [e2])
                  worker _ =mzero
           rmOneParam pn
              =applyTP (stop_tdTP (failTP `adhocTP` worker))
                where
                  worker (Exp (HsApp e1 e2 ))
                    |expToPN e1==pn =return e1
                  worker _ =mzero
      
       -----------remove parameters in demotedDecls-------------------------------
       rmParamsInDemotedDecls ps 
         =applyTP (once_tdTP (failTP `adhocTP` worker))  
            where worker ((HsMatch loc1 name pats rhs ds)::HsMatchP)
                    = do let pats'=filter (\x->not ((patToPN x /=defaultPN) && 
                                          elem (patToPN x) ps)) pats
                         pats'<-update pats pats' pats                            
                         return (HsMatch loc1 name pats' rhs ds)

    
       ----------remove parameters in the parent functions' rhs-------------------
       --Attention: PNT i1 _ _==PNT i2 _ _ = i1 =i2 
       rmParamsInParent  pn es
         =applyTP (full_buTP (idTP `adhocTP` worker))
            where worker exp@(Exp (HsApp e1 e2))
                   | findPN pn e1 && elem e2 es
                      =update exp e1 exp                      
                  worker (exp@(Exp (HsParen e1)))
                    |pn==expToPN e1
                       =update exp e1 exp
                  worker x =return x 
            
       getClashedNames oldNames newNames (match::HsMatchP)
         = do  (f,d)<-hsFDsFromInside match 
               ds'<-mapM (flip hsVisiblePNs match) oldNames
               -- return clashed names
               return (filter (\x->elem (pNtoName x) newNames)  --Attention: nub
                                   ( nub (d `union` (nub.concat) ds')))
       ----- make Substitions between formal and actual parameters.-----------------
       mkSubst pats params
           = catMaybes (zipWith (\x y ->if (patToPN x/=defaultPN) && (length (nub y)==1)
                            then Just (patToPN x,(ghead "mkSubst") y)
                            else Nothing) pats params)  
     

--substitute an old expression by new expression
replaceExpWithUpdToks  decls subst
   = applyTP (full_buTP (idTP `adhocTP` worker)) decls
         where worker (e::HsExpP)
                 |(expToPN e/=defaultPN) &&  (expToPN e)==(fst subst)
                     =update e (snd subst) e                      
               worker x=return x 


--return True if pn is a local function/pattern name
isLocalFunOrPatName pn scope
 =isLocalPN pn && isFunOrPatName pn scope


-- |removeTypeSig removes the signature declaraion for pn from the decl list.
removeTypeSig ::PName->[HsDeclP]->[HsDeclP]
removeTypeSig pn decls=concatMap (removeTypeSig' pn) decls
      where removeTypeSig' pn sig@(Dec (HsTypeSig loc is c tp))
             =if definesTypeSig pn sig && length is==1 
                 then []
                 else [Dec (HsTypeSig loc (filter (\x-> (pNTtoPN x)/=pn) is) c tp)]
            removeTypeSig' pn x=[x]   


-- |Divide a declaration list into three parts (before, parent, after) according to the PNT,
-- where 'parent' is the first decl containing the PNT, 'before' are those decls before 'parent'
-- and 'after' are those decls after 'parent'.

divideDecls::[HsDeclP]->PNT->([HsDeclP],[HsDeclP],[HsDeclP])
divideDecls ds pnt
  = let (before,after)=break (\x->findPNT pnt x) ds
    in if (after/=[])
         then (before, [ghead "divideDecls" after], tail after)
         else (ds,[],[])
 
