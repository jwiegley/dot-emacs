

module RefacADT(addFieldLabels,addDiscriminators,addConstructors,
                elimNestedPatterns,elimPatterns,createADTMod,fromAlgebraicToADT,
               fromAlgebraicToADT1) where
import Prelude hiding (putStrLn)
import Data.Maybe
import Data.List  
import Data.Char
import PrettyPrint 
import Prelude hiding (putStrLn)
import AbstractIO (putStrLn)
import PFE0 (allModules)

import RefacUtils hiding (mkNewName, conName)

-----------------------------------------------------------------------------------------------------
{-- This refactoring transforms an algebraic data type into an abstract datatype. This is done by
    composing the invloved primitive refactorings in a correct order.
-}
-----------------------------------------------------------------------------------------------------
-- two versions of 'fromAlgebraicToADT' with different user-interfaces.
fromAlgebraicToADT1 args 
   = do let fileName = ghead "filename" args
            typeCon  = (args!!1)
        seqRefac [addFieldLabels1 typeCon  fileName
                  ,addDiscriminators1 typeCon fileName
                  ,addConstructors1  typeCon fileName
                  ,elimNestedPatterns1 typeCon fileName
                  ,elimPatterns1 typeCon fileName 
                  ,createADT1 typeCon fileName                  
                  ]
        putStrLn "Refactoring completed." 

fromAlgebraicToADT args
  = do let fileName = ghead "filename" args
           row = read (args!!1)::Int 
           col = read (args!!2)::Int
       info@(_, _, mod, _)<-parseSourceFile fileName    
       case checkCursor fileName row col mod of
         Left errMsg ->do putStrLn errMsg
         Right decl  ->
            do let typeCon = pNtoName $ getTypeCon decl  
               seqRefac [addFieldLabels1 typeCon  fileName
                         ,addDiscriminators1 typeCon fileName
                         ,addConstructors1  typeCon fileName
                         ,elimNestedPatterns1 typeCon fileName
                         ,elimPatterns1 typeCon fileName 
                         ,createADT1 typeCon fileName                  
                         ]
               putStrLn "Refactoring completed."
--------------------------------------------------------
--This refactoring does not confined this refactoring.
seqRefac=seqRefac'.addFlagParam
 where  
    addFlagParam [] = []
    addFlagParam (r:rs) = (r False): (map (\r'->r' True) rs)
                      
    seqRefac' []= return ()                                 
    seqRefac' (r:rs) = do r 
                          seqRefac' rs 

----------------------------------------------------------------- 
addFieldLabels1 typeCon fileName isSubRefactor
 = do  info@(_, _, mod,_) <-parseSourceFile fileName 
       case findDataTypeDecl typeCon mod of 
        Left errMsg ->do putStrLn errMsg
        Right decl  ->addFieldLabels' info decl fileName isSubRefactor

addDiscriminators1 typeCon fileName isSubRefactor
  = do info@(_,_, mod,_) <- parseSourceFile fileName  
       case findDataTypeDecl typeCon mod of 
         Left errMsg -> putStrLn errMsg
         Right decl ->addDiscriminators' info decl fileName isSubRefactor      

addConstructors1 typeCon  fileName isSubRefactor
   = do info@(_, _,mod,_) <- parseSourceFile fileName
        case findDataTypeDecl typeCon mod of 
          Left errMsg -> putStrLn errMsg
          Right decl ->  addConstructors' info decl fileName isSubRefactor 

elimNestedPatterns1 typeCon fileName isSubRefactor
  = do info@(_,_,mod,_) <- parseSourceFile fileName
       case findDataTypeDecl typeCon mod of 
         Left errMsg -> putStrLn errMsg
         Right decl  -> elimNestedPatterns' decl info fileName isSubRefactor

elimPatterns1 typeCon fileName isSubRefactor
  = do info@(_,_,mod,_) <- parseSourceFile fileName
       case findDataTypeDecl typeCon mod of 
         Left errMsg -> putStrLn errMsg
         Right decl  -> elimPatterns' decl info fileName isSubRefactor

createADT1 typeCon fileName isSubRefactor 
  = do info@(_,_,mod,_) <- parseSourceFile fileName
       case findDataTypeDecl typeCon mod of 
         Left errMsg -> putStrLn errMsg
         Right decl  -> createADT' decl info fileName isSubRefactor

findDataTypeDecl::String->HsModuleP->Either String HsDeclP 
findDataTypeDecl typeCon mod
  = case find definesTypeCon (hsModDecls mod) of
        Nothing   -> Left "The refactorer could not find the datatype declaration."
        Just decl'-> Right decl'
  where
     definesTypeCon (Dec (HsDataDecl loc c tp _ _))
        = typeCon == pNTtoName (head (hsPNTs tp))
     definesTypeCon _ = False 


-------------------------------------------------------------------------------------------------------------
{- This refactoring creates the module interface for the ADT. The pre-condition for the
   refactoring is that there are no uses of the related data constructors in the importing modules.
  If this refactoring is only used as a basic step in the refactoring 'fromAlgebraicToADT', then there
  is no need to modify the client modules. However, if it is applied individully, there is a need to
  check the client modules to make sure the exporting does not cause name clash/conflict problems.
-}

createADTMod args
  =do let fileName= ghead "filename" args   
          row = read (args!!1)::Int
          col = read (args!!2)::Int   
      info@(_,_,mod,_) <- parseSourceFile fileName
      case checkCursor fileName row col mod of
        Left errMsg ->putStrLn errMsg
        Right decl  ->
           do isUsed<-useOfDataCons decl fileName  
              case isUsed of
                True ->putStrLn ("Some of the data constructors declared by this datatype are used by at"
                                  ++" least one of the client modules, please apply the 'eliminate patterns' refactoring first.")
                False->createADT' decl info fileName False 

-- check whether any of the declared constructors is used by client modules.
-- useOfDataCons::HsDeclP->ModuleName->HsModuleP->Maybe Bool

useOfDataCons decl fileName  
  = do  clients <-clientModsAndFiles =<<RefacUtils.fileNameToModName fileName  
        info <-mapM parseSourceFile (map snd clients)
        let pns =concatMap (findPNames  (conName decl)) (map (\ (_,_,mod,_)->hsModDecls mod) info)
        return (pns/=[])
  where 
       -- CHECK THIS LATER, WHY USING  findPNames from the API does not work.
       findPNames pns=head.(applyTU (once_tdTU (failTU `adhocTU` worker)))
        where 
          worker (pn1::PNT)
             |elem (pNTtoPN pn1) pns =return [pn1]
          worker _ =return []
  

createADT' decl (_, exps, mod, toks) fileName isSubRefactor
  = do (mod', ((toks',m),_)) <-runStateT (doCreateADTMod decl exps mod) ((toks, unmodified), (-1000, 0))
       serverModName<- RefacUtils.fileNameToModName fileName  
       clients<-clientModsAndFiles serverModName
       let typeCon = getTypeCon decl 
       refactoredClients <- mapM (createADTInClientMod typeCon)  clients
       writeRefactoredFiles isSubRefactor $ ((fileName,True),(toks', mod')):refactoredClients
       

createADTInClientMod typeCon (m, fileName)
   = do (_,_,mod,toks)<-parseSourceFile fileName
        (mod',((toks',modified),_))
           <-runStateT (rmSubEntsFromExport typeCon mod) ((toks,unmodified), (-1000,0))
        return ((fileName, modified),(toks',mod'))  


doCreateADTMod decl@(Dec (HsDataDecl _ _ _ cons _)) exps mod 
  = mkADTInterface exps typeCon (typeCon:(selectors++discriminators++constructors)) mod    
  where 
   typeCon = getTypeCon decl
   discriminators = map (fromJust.snd)  $ existingDiscriminators mod decl  
   constructors   = map (fromJust.snd) $ filter (\(x,y)->isJust y) $ existingConstructors mod decl
   selectors      = concatMap selectors' cons
     where  selectors' ((HsRecDecl _ _ _ i ts):: HsConDeclP) = map pNTtoPN (concatMap fst ts)
            selectors' ((HsConDecl _ _ _ i _) ::HsConDeclP)  = []


mkADTInterface exps typeCon pns mod 
  = case hsModExports mod of
          -- The whole module is implicitly exported.
         Nothing     -> addItemsToExport  mod  Nothing True (Right entsToBeExported) 
         -- There are explicitly exported entities.
         Just exports ->
           case isJust (find (==(ModuleE (hsModName mod))) exports) of
                  -- The module name is explicitly exported.
            True   -> do mod'<-rmItemsFromExport mod (Left ([sNtoName (hsModName mod)], pns))
                         addItemsToExport mod' Nothing True (Right entsToBeExported)
                         --individual entities are explicitly exported                            
            False  ->do let entsToAdd =map pNtoVarEnt $ (pns \\(findEnts pns exports))
                        -- remove the type constructor
                        mod'<-rmItemsFromExport mod (Left ([], [typeCon]))
                        addItemsToExport mod' Nothing True (Right ((pNtoVarEnt typeCon):entsToAdd))
  where
     -- entities need to be exported.
     entsToBeExported = nub $ map fromJust $ filter isJust (map fromEntToEntE exps)

     fromEntToEntE  (_, Ent modName (HsCon con) (Type _))
          = if sNtoName con == pNtoName typeCon  
              then -- only export type constructor.
                   Just $ EntE (Abs (nameToPNT (sNtoName con)))
                   -- export both type constructor and data constructor.
              else Just $ EntE (AllSubs (nameToPNT (sNtoName con)))
     fromEntToEntE  (_, Ent modName (HsVar var) _) 
          = Just $ EntE (Var (nameToPNT (sNtoName  var)))
     fromEntToEntE  _   = Nothing 
     
     findEnts pns ents
       =filter (\pn->any (\e->case e of 
                          ModuleE _ -> False
                          EntE e'   -> match pn e') ents) pns      
       where  match pn (Var pnt)        = pNTtoPN pnt == pn
              match pn (Abs pnt)        = pNTtoPN pnt == pn
              match pn (AllSubs pnt)    = pNTtoPN pnt == pn
              match pn (ListSubs pnt _) = pNTtoPN pnt == pn

------------------------------------End of createADTMod------------------------------------------------------

doCreateADTMod1 decl@(Dec (HsDataDecl _ _ _ cons _))  mod exps
  = addToExport mod exps typeCon (typeCon:(selectors++discriminators++constructors))     
  where 
   typeCon = getTypeCon decl
 
   discriminators = map (fromJust.snd)  $ existingDiscriminators mod decl  

   constructors   = map (fromJust.snd) $ filter (\(x,y)->isJust y) $ existingConstructors mod decl
   
   selectors      = concatMap selectors' cons
    
   selectors' ((HsRecDecl _ _ _ i ts):: HsConDeclP) = map pNTtoPN (concatMap fst ts)
   selectors' ((HsConDecl _ _ _ i _)::HsConDeclP)   = []

   addToExport mod exps typeCon pns 
    =let filteredExps =map fromJust $ filter isJust (map fromEntToEntE exps)
         exports = hsModExports mod 
         modName =ModuleE $ hsModName mod 
     in  case isNothing exports of
         True   -> return mod
         -- There are explicitly exported entities.
         False  -> case isJust (find (==modName) (fromJust exports))
                        of  -- The whole module is exported.
                          True   -> return mod
                           --   individual entities are explicitly exported                            
                          False  ->do let entsToAdd =map pNtoVarEnt $ (pns \\(findEnts pns (fromJust exports)))
                                      addItemsToExport mod Nothing False (Right entsToAdd)
      where   
        fromEntToEntE  (_, Ent modName (HsCon con) (Type _))
             = if sNtoName con == pNtoName typeCon  
                 then Just $ EntE (Abs (nameToPNT (sNtoName con)))
                 else Just $ EntE (AllSubs (nameToPNT (sNtoName con)))
        fromEntToEntE  (_, Ent modName (HsVar var) _) 
            = Just $ EntE (Var (nameToPNT (sNtoName  var)))
        fromEntToEntE  _   = Nothing 
     
        findEnts pns ents
         =filter (\pn->any (\e->case e of 
                           ModuleE _ -> False
                           EntE e'   -> match pn e') ents) pns      
          where  match pn (Var pnt)        = pNTtoPN pnt == pn
                 match pn (Abs pnt)        = pNTtoPN pnt == pn
                 match pn (AllSubs pnt)    = pNTtoPN pnt == pn
                 match pn (ListSubs pnt _) = pNTtoPN pnt == pn

exportEnts (HsModule _ _ (Just ents) _ _)
  = map fromJust $ filter isJust 
      ( map (\e ->case e of 
                  (EntE ent) ->Just ent 
                  _          ->Nothing) ents)
exportEnts (HsModule _ _ Nothing _ _) = []

findEntsToAdd typeConPN selectors discriminators constructors  ents
  = nub $ concatMap (match typeConPN) ents      
    where 

      match typeConPN (AllSubs pnt)
         | pNTtoPN pnt == typeConPN
        = concatMap snd selectors ++ map snd (discriminators++constructors)
      match typeConPN (ListSubs pnt idents)    -- refactor this 
        | pNTtoPN pnt == typeConPN
        = let r1 = concatMap (\(dataCon, funs)->if elem (pNtoName dataCon) identNames
                                                 then funs 
                                                 else []) selectors 
              r2 = concatMap (\(dataCon, fun)->if elem (pNtoName dataCon) identNames
                                                then [fun] 
                                                else []) (discriminators++constructors)
          in r1++r2
       where
          identNames= map identToName  idents 
          identToName (HsVar i) = pNTtoName i
          identToName (HsCon i) = pNTtoName i
      match _ _ = []
                                  
getTypeCon::HsDeclP->PName
getTypeCon decl@(Dec (HsDataDecl l c tp cons d))
  = pNTtoPN $ ghead "getTypeCon" $ filter (\(PNT _ (Type _) _)->True) (hsPNTs tp)

----------------------------------------------------------------------------------------------
{- This refactoring eliminate the affected patterns by using selectors/discriminators/constructors.
   The condition for this refactoring is that there shoudn't be any nested patterns using other data
   constructors in the pattern to be eliminated, and the selectors/discriminators/constructors should
   be available. So there is a need to modify the imports/exports interfaces to make sure these
   special functions are available. -}
  
----------------------------------------------------------------------------------------------  

elimPatterns args
 =do let fileName= ghead "filename" args            
         row = read (args!!1)::Int
         col = read (args!!2)::Int   
     info@(_,_,mod,_) <- parseSourceFile fileName
     case checkCursor fileName row col mod of
       Left errMsg -> putStrLn errMsg
       Right decl  -> elimPatterns' decl info fileName False
 

elimPatterns' decl (_, exps, mod, toks) fileName isSubRefactor
  = do (mod',((toks',modified),_))<-runStateT (do mod'<-doCreateADTMod1 decl mod exps
                                                  rmPatterns mod')
                                              ((toks,unmodified),(-1000,0)) 
       if (any (flip isExported  exps) (conPNT decl)) -- check whether any of the data constructors are exported.
         then do 
                 serverModName<- RefacUtils.fileNameToModName fileName  
                 clients<-clientModsAndFiles serverModName
                 refactoredClients <- mapM (elimPatternsInClientMod serverModName)  clients
                 writeRefactoredFiles isSubRefactor $ ((fileName,True),(toks', mod')):refactoredClients
         else writeRefactoredFiles isSubRefactor $ [((fileName,True),(toks', mod'))]
   where
     typeCon = getTypeCon decl

     conNames = conName decl

     selectors = gatherSelectors decl

     discriminators = gatherDiscriminators decl mod  

     constructors  = gatherConstructors decl mod               

     elimPatternsInClientMod serverModName (m, fileName)
       = do (_,_,mod,toks)<-parseSourceFile fileName
            (mod',((toks',modified),_))
                <-runStateT (do -- replace  exports of data constructors by exports of associated special functions.
                                 let entsToAdd= map (\x->(EntE (Var (nameToPNT x))))
                                             $ findEntsToAdd typeCon selectors discriminators constructors (exportEnts mod)
                                 mod'<- addItemsToExport mod Nothing False (Right entsToAdd)
                                 -- replace imports of data constructors by imports of associated special functions.
                                 mod''<-addToImport serverModName typeCon selectors  discriminators constructors mod'
                                 rmPatterns mod'')
                             ((toks,unmodified), (-1000,0))
            return ((fileName, modified),(toks',mod'))  

     rmPatterns = applyTP (full_tdTP (idTP `adhocTP` inMatch           -- full_buTP and full_tdTP make difference in this function.
                                           `adhocTP` inPatBinding
                                           `adhocTP` inExp)) 
  
       where  

         inMatch (match@(HsMatch loc i ps rhs ds)::HsMatchP) 
           |isNothing (find (==(pNTtoName i)) (map snd (discriminators++constructors))) 
            --the condition ensures that those special funs are not affected.
           = do (ps', sels, guards) <-rmPatternsInParams conNames match ps
                rhs'<-replaceVarsBySels sels rhs
                rhs''<-replacePatsByConstructors conNames constructors rhs'
                rhs'''<-if guards/=[] then addGuardsToRhs rhs'' $ fromJust (mkGuard guards)
                                      else return rhs''                                    
                ds'<-replacePatsByConstructors conNames constructors =<<replaceVarsBySels sels ds 
                return $ (HsMatch loc i ps' rhs''' ds')   
         inMatch m = return m
 
         inPatBinding (pat@(Dec (HsPatBind loc i rhs ds)::HsDeclP)) 
           |isNothing (find (==(pNTtoName.patToPNT) i) (map snd (discriminators++constructors)))
            --the condition ensures that those special funs are not affected.
           = do rhs'<-replacePatsByConstructors conNames constructors rhs                           
                ds'<-replacePatsByConstructors conNames constructors  ds 
                return $ (Dec (HsPatBind loc i rhs' ds'))
         inPatBinding m = return m
       
         inExp (exp@(Exp (HsLambda ps e))::HsExpP)
           =do (ps', sels, guards) <-rmPatternsInParams conNames exp ps        
               e'<-replaceVarsBySels sels e
               let e''= if guards/=[] then (Exp (HsCase (fromJust (mkGuard guards))
                                            [HsAlt loc0 fakeTruePat (HsBody e') []]))
                                      else e'
                   exp'= Exp (HsLambda ps' e'')
               if (exp/=exp') then update exp exp' exp
                              else return exp'        


         inExp exp@(Exp (HsListComp stmts))
           = do exp'<-applyTP (full_buTP (idTP `adhocTP` inStmt)) exp  
                if (exp/=exp') then update exp exp' exp
                               else return exp'
           where 
             inStmt (stmt@(HsGenerator loc p e stmts)::HsStmtP)
               = do (p', sels, guards) <-rmPatternsInParams conNames stmt p      
                    e'<-replaceVarsBySels sels e
                    stmts'<-replaceVarsBySels sels stmts
                    let stmts''=if guards/=[] then (HsQualifier (fromJust (mkGuard guards)) stmts')
                                              else stmts'    
                    return $ HsGenerator loc p' e' stmts''                                    
             inStmt m = return m  

         inExp exp@(Exp (HsDo stmts))
            = do exp' <-applyTP (full_buTP (idTP `adhocTP` inStmt)) exp 
                 if (exp/=exp') then update exp exp' exp                           
                                else return exp'
           where 
             inStmt (stmt@(HsGenerator loc p e stmts)::HsStmtP)
               =do (p', sels, guards) <-rmPatternsInParams conNames stmt p     
                   e'<-replaceVarsBySels sels e
                   stmts'<-replaceVarsBySels sels stmts
                   let stmts''=if guards/=[] then (HsLast (Exp (HsCase (fromJust (mkGuard guards))
                                                   [HsAlt loc0 fakeTruePat (HsBody (Exp (HsDo stmts'))) []])))
                                             else stmts'
                   return (HsGenerator loc p' e' stmts'')           
             inStmt m = return m

         inExp exp@(Exp (HsCase e alts))
           = do exp'<-applyTP (full_buTP (idTP `adhocTP` inAlt)) exp 
                if (exp/=exp') then update exp exp' exp                               
                               else return exp'            
           where 
            inAlt (alt@(HsAlt loc p rhs ds)::HsAltP)
              = do  (p', sels, guards) <-rmPatternsInParams conNames alt p 
                    rhs'<- replaceVarsBySels sels rhs    
                    rhs''<-if guards/=[] then addGuardsToRhs rhs' $ fromJust (mkGuard guards)
                                         else return rhs'                                      
                    ds'<-replaceVarsBySels sels ds
                    return (HsAlt loc p' rhs'' ds') 
         inExp m = return m


         rmPatternsInParams conNames ast ps
           = do fds <-existingVbls ast
                ps' <- rmPatternInParams1 fds conNames ps
                resetVal
                (sels, guards) <-rmPatternInParams2 fds conNames ps
                resetVal
                return (ps',sels, guards)
            where 
          -- Two versions of `rmPatternInParams`, one for transformation, one for collecting information.
         rmPatternInParams1 d conNames  
            =applyTP (stop_tdTP (failTP `adhocTP` inPat)) 
             where
             inPat pat@(Pat (HsPParen (Pat (HsPApp i is))))
              | isJust (find (==pNTtoPN i) conNames) 
              = inPat' pat Nothing        
             inPat pat@(Pat (HsPAsPat i1 (Pat (HsPParen (Pat (HsPApp i2 is))))))
              | isJust (find (==pNTtoPN i2) conNames)
              = inPat' pat (Just (pNTtoName i1))
             inPat (pat@(Pat (HsPApp i is))::HsPatP)
              | isJust (find (==pNTtoPN i) conNames) 
              = inPat' pat Nothing 
             inPat pat@(Pat (HsPAsPat i1 (Pat (HsPApp i2 is))))
               | isJust (find (==pNTtoPN i2) conNames) 
              = inPat' pat (Just (pNTtoName i1))
             inPat pat@(Pat (HsPId (HsCon i)))
               | isJust (find (==pNTtoPN i) conNames)
              =inPat' pat Nothing
             inPat pat@(Pat (HsPParen (Pat (HsPId (HsCon i)))))
               | isJust (find (==pNTtoPN i) conNames)
              = inPat' pat Nothing
             inPat pat@(Pat (HsPAsPat i1 (Pat (HsPId (HsCon i2)))))
               | isJust (find (==pNTtoPN i2) conNames)
              =inPat' pat (Just (pNTtoName i1))
             inPat pat@(Pat (HsPAsPat i1 (Pat (HsPParen (Pat (HsPId (HsCon i2)))))))
               | isJust (find (==pNTtoPN i2) conNames)
              =inPat' pat (Just (pNTtoName i2))
              
             inPat _ = mzero
         
             inPat' pat varName 
                = do unless (not (isNestedPattern conNames pat))
                         $ error "Nested patterns exist, please apply the 'eliminate nested patterns' refactoring first!"
                     (_,d') <- hsFreeAndDeclaredPNs pat   
                     (tm,(v,val)) <- get
                     let newVarName =if isJust varName then fromJust varName
                                                       else mkNewName "p" (map pNtoName (d\\d')) "" val
                         nextVal' =(ord (glast "rmPatternInParams'" newVarName) - ord '0') +1 
                         nextVal = if nextVal' >10 then 1 else nextVal'                            
                     put (tm, (v,nextVal))                
                     update pat  (Pat (HsPId (HsVar (nameToPNT newVarName)))) pat
 
         rmPatternInParams2 d conNames ps
           =do r<-applyTU (stop_tdTU (failTU `adhocTU` inPat)) ps
               return (concatMap fst r, concatMap snd r)
           where
             inPat (pat@(Pat (HsPApp i is))::HsPatP)
               | isJust (find (==pNTtoPN i) conNames)
               = inPat' (pNTtoPN i) pat Nothing
 
             inPat (pat@(Pat (HsPId (HsCon i)))::HsPatP)
               | isJust (find (==pNTtoPN i) conNames)
               = inPat' (pNTtoPN i) pat Nothing

             inPat (pat@(Pat (HsPAsPat i1 i2)))
                 | case rmPParen i2 of   
                       (Pat (HsPApp i2' _)) ->isJust (find (==pNTtoPN i2') conNames)
                       (Pat (HsPId (HsCon i2'))) ->isJust (find (==pNTtoPN i2') conNames)
                       _ ->False 
                 = (\pat -> case pat of 
                            (Pat (HsPApp i2' ps)) ->inPat' (pNTtoPN i2') pat (Just (pNTtoName i1))
                            (Pat (HsPId (HsCon i2')))->inPat' (pNTtoPN i2') pat (Just (pNTtoName i1))) (rmPParen i2)
             inPat _ =mzero

             inPat' conPN pat varName 
               = do (_,d') <- hsFreeAndDeclaredPNs pat  
                    (tm,(v,val)) <- get
                    let (newVarName,nextVal')
                           =if isJust varName
                              then (fromJust varName, val)
                              else (mkNewName "p" (map pNtoName (d\\d')) "" val, 
                                    (ord (glast "rmPatternInParams'" newVarName) - ord '0') +1)
                        nextVal = if nextVal' >10 then 1 else nextVal'
                    put (tm,  (v,nextVal))                
                    let sels = findSelectors conPN selectors 
                        selectorFuns =mkSelectorFuns conPN newVarName "" sels pat                         
                        guardExps = mkGuardExps newVarName discriminators pat                      
                    return [(selectorFuns, guardExps)]

         isNestedPattern conNames appPat
             = isJust $ find (==True) (ghead "isNestedPattern" (isNestedPattern' appPat))
           where
            isNestedPattern'= applyTU (full_tdTU (constTU []  `adhocTU` inAppPat))
              where
               inAppPat pat
                 | isVarPat pat =return []
               inAppPat pat@(Pat (HsPApp i ps))
                 |isJust (find (==pNTtoPN i) conNames)
                 = return []
               inAppPat pat@(Pat (HsPId (HsCon i)))
                 |isJust (find (==pNTtoPN i) conNames)
                 =return []       
               inAppPat pat@(Pat (HsPInfixApp _ i _))
                 |isJust (find (==pNTtoPN i) conNames)
                 = return []
               inAppPat pat@(Pat (HsPRec i _))
                 |isJust (find (==pNTtoPN i) conNames)
                 = return [] 
               inAppPat pat@(Pat (HsPAsPat i1 i2)) 
                 =isNestedPattern' i2
               inAppPat pat@(Pat (HsPParen p))
                 =isNestedPattern' p               
               inAppPat _ = return [True]

         repalceVarsBySels [] p = return p
         replaceVarsBySels sels p =applyTP (full_buTP (idTP `adhocTP` inExp)) p
           where 
             inExp exp@(Exp (HsId (HsVar (PNT pn ty src@(N (Just (SrcLoc fileName  c row col))))))) 
                |isJust (find (==pn) pnsToBeReplaced)
               = do let sel = (snd.fromJust) (find (\(x,y)-> x==pn) sels)
                        --pn' = replaceNameInPN Nothing pn sel  
                    update exp sel exp 
                    --update pnt (PNT pn' ty src) pnt                   
             inExp e = return e      
             pnsToBeReplaced =map fst sels

         replacePatsByConstructors conNames constructors 
            = applyTP (full_tdTP (idTP `adhocTP` inExp))
                                       -- `adhocTP` inPNT))
           where
            inExp exp@(Exp (HsRecConstr _ i fields)) 
              | isJust (find (==pNTtoPN i) conNames)
               = do let entry = find (\(x,y)->x==(pNTtoPN i)) constructors
                        con   = if isJust entry 
                                 then (snd.fromJust) entry
                                 else error $ "Constructor function does not exist for the data constructor:" ++ pNTtoName i
                        es = map (\(HsField _ e ) -> e) fields
                        exp'= (Exp (HsParen (foldl (\e1 e2->(Exp (HsApp e1 e2))) (nameToExp con) es)))
                    update exp exp' exp                    
            inExp e 
              | isJust (find (==(pNTtoPN.expToPNT) e) conNames)
              = do let (PNT pn ty src)=expToPNT e 
                       entry = find (\(x,y)->x==pn) constructors
                       constructor 
                         =if isJust entry 
                           then (snd.fromJust) entry
                           else error $ "Constructor function does not exist for the data constructor:"++ pNtoName pn
                   renamePN pn Nothing constructor True e

            inExp e = return e             
            
{-
            inPNT pnt@(PNT pn ty src@(N (Just (SrcLoc fileName  c row col))))
              | isJust (find (== pn) conNames) && not (isTypeCon pnt)
              = do let entry = find (\(x,y)->x==pn) constructors
                       constructor = if isJust entry 
                                       then (snd.fromJust) entry
                                       else error $ "Constructor function does not exist for the data constructor:"++ pNtoName pn
                       pn' = replaceNameInPN Nothing pn constructor
                   updateExpToks pnt constructor
                   return (PNT pn' ty src)
            inPNT pnt = return pnt 
-}
       
         mkGuardExps newVarName discriminators (Pat (HsPApp i ps))
           = let discr =findDiscriminator (pNTtoPN i)  discriminators 
                 guardExp=Exp (HsApp (Exp (HsId (HsVar (nameToPNT discr))))
                           (Exp (HsId (HsVar (nameToPNT newVarName)))))
             in [guardExp]

         mkGuardExps newVarName discriminators (Pat (HsPId (HsCon i)))
           = let discr =findDiscriminator (pNTtoPN i)  discriminators 
                 guardExp=Exp (HsApp (Exp (HsId (HsVar (nameToPNT discr))))
                           (Exp (HsId (HsVar (nameToPNT newVarName)))))
             in [guardExp]
         mkGuard [] = Nothing
         mkGuard (e:es)
           = Just (foldl (\e1 e2 -> (Exp (HsInfixApp e1 (HsVar (nameToPNT  "&&")) e2))) e es)

         -- What is poxfix for?
         mkSelectorFuns con  newVarName posfix selectors (Pat (HsPApp i ps)) 
          = concatMap mkSelectorFuns' (zip selectors ps)
          where mkSelectorFuns' (sel, pat@(Pat (HsPId (HsVar i))))
                  =[(pNTtoPN i, if posfix ==[]
                                    then  (Exp (HsParen (Exp (HsApp (Exp (HsId (HsVar (nameToPNT sel))))
                                                (Exp (HsId (HsVar (nameToPNT newVarName))))))))
                                    else (Exp (HsParen (Exp (HsApp (Exp (HsId (HsVar (nameToPNT (sel++"."++posfix)))))
                                                           (Exp (HsId (HsVar (nameToPNT newVarName)))))))))]
                                   {-                  
                                      if posfix=="" then "("++sel++" "++ newVarName++")"
                                               else "(("++sel++"."++posfix++") "++newVarName++")")] -}
                mkSelectorFuns' (sel, (Pat (HsPParen p)))
                 = mkSelectorFuns' (sel, p)
                mkSelectorFuns' (sel, pat@(Pat (HsPApp i ps)))
                 = mkSelectorFuns con newVarName
                      (if posfix=="" then sel else sel++"."++posfix) selectors pat  
                mkSelectorFuns' (sel, _) = [] 
         mkSelectorFuns _ _ _ _  _ = []


---- This function is only used by the 'RefacADT.hs' module, I haven't work out a way to refactor it.
addToImport serverModName typeCon selectors discriminators constructors mod
  =applyTP (full_buTP (idTP `adhocTP` inImport)) mod
  where 
    inImport (imp@(HsImportDecl loc m@(SN modName _) qual  as h):: HsImportDeclP)
      | serverModName == modName &&  findPN typeCon h
       = case h of
           Nothing        -> return imp                     
           Just (b, ents) -> do let funs=findEntsToAdd typeCon selectors discriminators constructors ents
                                if (funs==[]) then return imp
                                  else addItemsToImport serverModName Nothing (Left funs) imp
    inImport imp = return imp

   
    findEntsToAdd typeConPN selectors discriminators constructors ents
      = nub $ concatMap (match typeConPN) ents      
      where 

      match typeConPN (AllSubs pnt)
         | pNTtoPN pnt == typeConPN
        = concatMap snd selectors ++ map snd (discriminators++constructors)
      match typeConPN (ListSubs pnt idents)    -- refactor this 
        | pNTtoPN pnt == typeConPN
        = let r1 = concatMap (\(dataCon, funs)->if elem (pNtoName dataCon) identNames
                                                 then funs 
                                                 else []) selectors 
              r2 = concatMap (\(dataCon, fun)->if elem (pNtoName dataCon) identNames
                                                then [fun] 
                                                else []) (discriminators++constructors)
          in r1++r2
       where
          identNames= map identToName  idents 
          identToName (HsVar i) = pNTtoName i
          identToName (HsCon i) = pNTtoName i
      match _ _ = []
    
------------------------------------------------------------------------------------------------------------------------  
{- This refactoring removes the explict uses of specific data constructors by using selectors/disriminators/constructors.
   To do this refactoring, put the cursor at beginning of the data type declaration, then select the `elimNestedPatterns`
   in Refactor menu. There is no pre-condition for this refactoring.  -}
------------------------------------------------------------------------------------------------------------------------
elimNestedPatterns args
 =do let fileName= ghead "filename" args            
         row = read (args!!1)::Int
         col = read (args!!2)::Int   
     info@(inscps, exps, mod, toks) <- parseSourceFile fileName
     case checkCursor fileName row col mod of
       Left errMsg -> putStrLn errMsg
       Right decl  -> elimNestedPatterns' decl info fileName False                                             

elimNestedPatterns'  decl (_,_,mod,toks) fileName isSubRefactor
  = do (mod',((toks',modified),_))<-runStateT (elimNestedPatterns'' mod)
                                     ((toks,unmodified), (-1000,0))
       modName <- RefacUtils.fileNameToModName fileName  
       clients<-clientModsAndFiles modName   
       refactoredClients <- mapM elimNestedPatternsInClientMod  clients
       writeRefactoredFiles isSubRefactor $ ((fileName,True),(toks', mod')):refactoredClients
     
   where 

     conNames = conName decl 

     elimNestedPatternsInClientMod (m,fileName)
       = do (_,_,mod,toks)<-parseSourceFile fileName
            (mod',((toks',modified),_))<-runStateT (elimNestedPatterns''  mod)
                                          ((toks,unmodified), (-1000,0))
            return ((fileName, modified),(toks',mod'))   

      {- This function removes those nested patterns in the formal parameters of a function declaration
         by introducing guards and case expression. -}
     elimNestedPatterns'' = applyTP (full_buTP (idTP `adhocTP` inMatch 
                                                     `adhocTP` inExp))
      where  
       inMatch (match@(HsMatch loc i ps rhs ds)::HsMatchP) 
        = do newMatch <-mkNewAST mkNewMatch conNames match ps                
             if (match/=newMatch) then update match newMatch match
                                  else return newMatch 

       inExp (exp@(Exp (HsLambda ps e))::HsExpP)
         =do newLambdaExp <-mkNewAST mkNewLambdaExp conNames exp ps 
             if (exp/=newLambdaExp) then update exp newLambdaExp exp
                                    else  return newLambdaExp     

       inExp exp@(Exp (HsListComp stmts))
          = do exp'<-applyTP (full_buTP (idTP `adhocTP` inStmt)) exp  
               if (exp/=exp') then update exp exp' exp                                
                              else return exp'
          where 
           inStmt (stmt@(HsGenerator loc p e stmts)::HsStmtP)
             = mkNewAST mkNewListStmt conNames stmt p           
           inStmt m = return m  

       inExp exp@(Exp (HsDo stmts))
          = do exp' <-applyTP (full_buTP (idTP `adhocTP` inStmt)) exp 
               if (exp/=exp') then update exp exp' exp
                              else return exp'
         where 
           inStmt (stmt@(HsGenerator loc p e stmts)::HsStmtP)
              = mkNewAST mkNewDoStmt conNames stmt p     
           inStmt m = return m

       inExp exp@(Exp (HsCase e alts))
          = do exp'<-applyTP (full_buTP (idTP `adhocTP` inAlt)) exp  
               if (exp/=exp') then update exp exp' exp
                              else  return exp'            
          where 
            inAlt (alt@(HsAlt loc p rhs ds)::HsAltP)
              = mkNewAST mkNewAlt conNames alt p 
       inExp m = return m


     mkNewAST fun conNames ast p
       = do fds <-existingVbls ast
            p' <-rmNestedPatternInParams2 fds conNames p
            resetVal
            varsAndPats <- getExpPatPairs fds conNames p
            resetVal
            return (fun ast p' varsAndPats)

     mkNewDoStmt stmt@(HsGenerator loc p e stmts) p' varsAndPats
       =case varsAndPats of
            Nothing -> stmt
            Just (caseVars, casePats) -> (HsGenerator loc p' e (HsLast (Exp (HsCase caseVars
                                           [HsAlt loc0 casePats (HsBody (Exp (HsDo stmts))) []]))))
 
     mkNewListStmt stmt@(HsGenerator loc p e stmts) p' varsAndPats
       = case varsAndPats of
           Nothing -> stmt
           Just (caseVars,casePats) ->(HsGenerator loc p' e (HsGenerator loc casePats (Exp (HsList [caseVars])) stmts))

     mkNewLambdaExp exp@(Exp (HsLambda ps e)) ps' varsAndPats
      = case varsAndPats of
           Nothing -> exp
           Just (caseVars,casePats) -> (Exp (HsLambda ps' (Exp (HsCase caseVars [HsAlt loc0 casePats (HsBody e) []]))))
                                            
     mkNewAlt alt@(HsAlt loc p rhs@(HsBody e) ds) p' expsAndPats 
       = case expsAndPats of
            Nothing -> alt
            Just (exps, pats)->(HsAlt loc p' (HsGuard [(loc0, (Exp (HsCase exps 
                             [HsAlt loc0  pats (HsBody fakeTrueExp) [],
                             HsAlt loc0 (Pat HsPWildCard) (HsBody fakeFalseExp) []])), 
                            (Exp (HsApp (Exp (HsParen (Exp (HsLambda [pats] e)))) exps)))]) ds)

     mkNewAlt alt@(HsAlt loc p rhs@(HsGuard es) ds) p' expsAndPats
       = case expsAndPats of
             Nothing -> alt
             Just (exps, pats) -> let rhs'= HsGuard $ map (addToGuards (exps, pats)) es 
                                  in (HsAlt loc p' rhs' ds)

     mkNewMatch ((HsMatch loc i ps rhs@(HsBody e) ds)::HsMatchP) ps' expsAndPats
       = case expsAndPats of
            Nothing -> HsMatch loc i ps' rhs ds
            Just (exps, pats) -> (HsMatch loc i ps' (HsGuard [(loc0, (Exp (HsCase exps 
                                 [HsAlt loc0  pats (HsBody fakeTrueExp) [],
                                 HsAlt loc0 (Pat HsPWildCard) (HsBody fakeFalseExp) []])), 
                                 (Exp (HsApp (Exp (HsParen (Exp (HsLambda [pats] e)))) exps)))]) ds)
          
     mkNewMatch (HsMatch loc i ps rhs@(HsGuard es) ds) ps' expsAndPats
       = case expsAndPats of 
          Nothing-> HsMatch loc i ps' rhs ds 
          Just (exps, pats)-> let rhs'= HsGuard $ map (addToGuards (exps,pats)) es 
                              in (HsMatch loc i ps' rhs' ds)

     addToGuards  (exp, pat) (loc, e1, e2)
       = let g1 = Exp (HsCase exp
                    [HsAlt loc0  pat (HsBody fakeTrueExp) [],
                     HsAlt loc0 (Pat HsPWildCard) (HsBody fakeFalseExp) []])
             e1'= Exp (HsInfixApp g1 (HsVar (nameToPNT "&&")) e1)
             e2'= Exp (HsApp (Exp (HsParen (Exp (HsLambda [pat] e2)))) exp)
         in (loc, e1', e2')

                     
     getExpPatPairs d conNames ps
       = do r <- applyTU (stop_tdTU (failTU `adhocTU` inPat)) ps
            let r' = filter (\(x,y) -> isJust x) r
                r''= map (\(x,y)->(patVarToExpVar (fromJust x),y)) r'
                (exps, pats) = (map fst r'', map snd r'')
            return (if length exps ==0 then Nothing
                    else if length exps==1 then Just (head exps, head pats)
                                           else Just (Exp (HsTuple exps), Pat (HsPTuple loc0 pats)))
        where
          inPat (pat@(Pat (HsPApp i is))::HsPatP)
            | isJust (find (==pNTtoPN i) conNames)
           = do  is'<-rmNestedPatternInParams1 d conNames is
                 let caseExps = filter (\(x,y) ->isJust x) is'
                 return caseExps
          inPat _ = mzero

          patVarToExpVar (Pat (HsPId (HsVar id))) = (Exp (HsId (HsVar id)))
     
     {-There are two versions of 'rmNestedPatternsInParams'. These two functions have different
       purspose: 'rmNestedPatternInParams1' aims to collect info, whereas 'rmNestedPatternInParams2'
       aims to modify the syntax tree and token stream. The reason for this is because of the 
       limitation of Strafunski's combinators-}
  
     rmNestedPatternInParams1 d conNames 
        = applyTU (stop_tdTU (failTU `adhocTU` inAppPat)) 
      where
       inAppPat pat
         | isVarPat pat = return [(Nothing, pat)]
       inAppPat pat@(Pat (HsPApp i ps))
         |isNothing (find (==pNTtoPN i) conNames)
          = replacePatByVar pat Nothing       
       inAppPat pat@(Pat (HsPAsPat i1 (Pat (HsPApp i2 ps))))
         |isNothing (find (==pNTtoPN i2) conNames)
         = replacePatByVar pat (Just (pNTtoName i1))        
       inAppPat pat@(Pat (HsPInfixApp _  i _))
         |isNothing (find (==pNTtoPN i) conNames)
          = replacePatByVar pat Nothing
       inAppPat pat@(Pat (HsPAsPat i1 (Pat (HsPInfixApp _ i2 _))))
         |isNothing (find (==pNTtoPN i2) conNames)
         = replacePatByVar pat (Just (pNTtoName i1))
       inAppPat pat@(Pat (HsPRec i _))
         |isNothing (find (==pNTtoPN i) conNames)
         = replacePatByVar pat Nothing 
       inAppPat pat@(Pat (HsPAsPat i1 (Pat (HsPRec i2 _))))
         |isNothing (find (==pNTtoPN i2) conNames)
         = replacePatByVar pat (Just (pNTtoName i1))
       inAppPat pat
        = replacePatByVar pat Nothing

       replacePatByVar pat varName
         = do (_,d') <- hsFreeAndDeclaredPNs pat
              (t,(v,val)) <- get 
              let (newVarName,nextVal')
                   =if isJust varName
                      then (fromJust varName, val)
                      else (mkNewName "p" (map pNtoName (d\\d')) "" val, 
                             (ord (glast "rmPatternInParams'" newVarName) - ord '0') +1)               
                  nextVal = if nextVal' >10 then 1 else nextVal'
              put (t, (v,nextVal))                
              return [(Just (Pat (HsPId (HsVar (nameToPNT newVarName)))), pat)]

     rmNestedPatternInParams2 d conNames 
       = applyTP (stop_tdTP (failTP `adhocTP` inPat))
       where
        inPat (pat@(Pat (HsPApp i is))::HsPatP)
          | isJust (find (==pNTtoPN i) conNames)
          = do is'<-rmNestedPatternInParams' is           
               return (Pat (HsPApp i is'))
        inPat _ = mzero 
        -- replace the nested patterns by variables.
        rmNestedPatternInParams' 
          = applyTP (stop_tdTP (failTP `adhocTP` inAppPat)) 
          where
           inAppPat pat
             | isVarPat pat = mzero
           inAppPat pat@(Pat (HsPApp i ps))
             |isNothing (find (==pNTtoPN i) conNames)
              = replacePatByVar pat Nothing       
           inAppPat pat@(Pat (HsPAsPat i1 (Pat (HsPApp i2 ps))))
             |isNothing (find (==pNTtoPN i2) conNames)
             = replacePatByVar pat (Just (pNTtoName i1))        
           inAppPat pat@(Pat (HsPInfixApp _ i  _))
             |isNothing (find (==pNTtoPN i) conNames)
             = replacePatByVar pat Nothing
           inAppPat pat@(Pat (HsPAsPat i1 (Pat (HsPInfixApp _  i2  _))))
             |isNothing (find (==pNTtoPN i2) conNames)
             = replacePatByVar pat (Just (pNTtoName i1))
           inAppPat pat@(Pat (HsPRec i _))
             |isNothing (find (==pNTtoPN i) conNames)
             = replacePatByVar pat Nothing 
           inAppPat pat@(Pat (HsPAsPat i1 (Pat (HsPRec i2 _))))
             |isNothing (find (==pNTtoPN i2) conNames)
             = replacePatByVar pat (Just (pNTtoName i1))
           inAppPat pat
             = replacePatByVar pat Nothing

           replacePatByVar pat varName 
             = do (_,d') <- hsFreeAndDeclaredPNs pat
                  (t,(v,val)) <- get
                  let (newVarName,nextVal')
                        =if isJust varName
                           then (fromJust varName, val)
                           else (mkNewName "p" (map pNtoName (d\\d')) "" val, 
                                 (ord (glast "rmPatternInParams'" newVarName) - ord '0') +1)      
                      nextVal = if nextVal' >10 then 1 else nextVal'                    
                  put (t,(v,nextVal)) 
                  update pat (Pat (HsPId (HsVar (nameToPNT newVarName)))) pat
---------------------------------------------------------------------------------
{- This refactoring adds field labels to a data type declaration, the label names will
   be created by the refactorer automatically, however the user can rename them afterwards.
   The refactoring does nothing if all the field labels already exisit.
   No pre-condition for this refactoring.
-}
addFieldLabels args
 =do let fileName= ghead "filename" args            
         row = read (args!!1)::Int
         col = read (args!!2)::Int   
     info@(inscps, exps, mod, toks) <- parseSourceFile fileName
     case checkCursor fileName row col mod of
       Left errMsg -> putStrLn errMsg
       Right decl  -> addFieldLabels' info decl fileName False

addFieldLabels' (inscps,_, mod, toks) decl fileName isSubRefactor
 = do clients <-clientModsAndFiles =<<RefacUtils.fileNameToModName fileName   
      -- make sure the new name does not cause any problems in the current and client modules.
      -- By doing this, the refactor does not need to check the clients.
      clientInfo <- mapM parseSourceFile (map snd clients) 
      let inscpNames =map (\ (x,_,_,_)->x) (concatMap inScopeInfo (inscps:(map (\ (a,_,_,_)->a) clientInfo)))
      (mod',((toks',modified),_))<-runStateT (addFieldLabels'' inscpNames decl mod) ((toks, unmodified), (-1000,0))
      writeRefactoredFiles isSubRefactor $ [((fileName,True),(toks', mod'))]
    
addFieldLabels'' inscpNames decl mod 
  = do let (decls1, decls2) = break (==decl) (hsModDecls mod)
       newDecl <-conDeclToRecDecl inscpNames decl
       decl'<-update decl newDecl decl
       return $ mod {hsModDecls=decls1++(decl':(tail decls2))}
 
-- Add field labels to each data constructor declaration.  
conDeclToRecDecl inscpeNames = applyTP (full_buTP (idTP `adhocTP` inConDecl)) 
   where
   inConDecl (decl@(HsConDecl loc is c i ts):: HsConDeclP)
     |ts /= [] 
      = do ts'<-createFieldLabel 1 i ts
           return (HsRecDecl loc is c i ts')
   inConDecl x = return x -- already has field labels.
   -- create a field label by attaching a number to the end of the data constructor name.
   createFieldLabel val dataCon [] = return []
   createFieldLabel val dataCon (t:ts)
    = do let name = mkNewName (map toLower (pNTtoName dataCon)) inscpeNames "" val
             fieldLabelPNT =(PNT (PN (UnQual name) (G (PlainModule "unknown") name
                                  (N (Just loc0)))) Value (N (Just loc0)))
             -- only allowing one digit is too restrictive. 
             nextVal = (ord (glast "createFieldLabel" name) - ord '0') + 1
         ds' <- createFieldLabel nextVal dataCon ts           
         return $ ([fieldLabelPNT], t):ds'


--------------------------------------------------------------------------------------
{- This refactoring adds discriminator functions to a data type declaration. The function names
   will be created by the refactorer automatically, however the user can rename them afterwards.
   No pre-condition for this refactoring.
-}

addDiscriminators args
 =do let fileName= ghead "filename" args            
         row = read (args!!1)::Int
         col = read (args!!2)::Int   
     info@(inscps, exps, mod, toks) <- parseSourceFile fileName
     case checkCursor fileName row col mod of 
       Left errMsg -> putStrLn errMsg
       Right decl  -> addDiscriminators' info decl fileName False

addDiscriminators' (inscps,_,mod,toks) decl fileName isSubRefactor
  = do clients <-clientModsAndFiles =<< RefacUtils.fileNameToModName fileName   
       clientInfo <- mapM parseSourceFile (map snd clients) 
       let inscpNames= map (\(x,_,_,_)->x) (concatMap inScopeInfo (inscps:(map (\(a,_,_,_)->a) clientInfo)))
       (mod',((toks',modified),_))<-runStateT (addDiscriminators'' inscpNames decl mod)((toks, unmodified), (-1000,0))
       -- no need to modify the client module.
       writeRefactoredFiles isSubRefactor $  [((fileName,True),(toks',mod'))]

addDiscriminators'' inscpNames decl@(Dec (HsDataDecl (SrcLoc  _ _ _ col) c tp conDecls _)) mod 
   = do let consWithDiscrs = existingDiscriminators mod decl
        if (length conDecls == length consWithDiscrs)
          then return mod  -- all the discriminators already exist.           
          else do     -- those data constructor decls without discriminators.
                  let conDecls' = filter (\x->isNothing (find (conName' x==) (map fst consWithDiscrs))) conDecls
                      funs= concatMap (mkDiscriminator col tp inscpNames (length conDecls) mod) conDecls'
                  addDecl mod Nothing (funs,Nothing) True 
   where             
     mkDiscriminator startCol tp existingNames cons mod (decl@(HsRecDecl _ _ _ i ts):: HsConDeclP)
       = mkDiscriminator' startCol tp existingNames cons mod i ts 
     mkDiscriminator startCol tp existingNames cons mod (decl@(HsConDecl _ _ _ i ts):: HsConDeclP)
       = mkDiscriminator' startCol tp existingNames cons mod i ts 
      
     mkDiscriminator' startCol tp existingNames cons mod i ts 
       = let funNamePNT =nameToPNT $  mkNewName (pNTtoName i) existingNames "is" 0 
             typeSig = (Dec (HsTypeSig loc0 [funNamePNT] [] (Typ (HsTyFun tp (Typ (HsTyCon (PNT (PN
                         (UnQual "Bool") (G (PlainModule "Prelude") "Bool" (N (Just loc0)))) 
                        (Type blankTypeInfo) (N (Just loc0 )))))))))
             -- if only one data constructor is declared, only one match is needed.
             match1 =let pats= if length ts ==0 then [Pat (HsPId (HsCon i))]
                                                else [Pat (HsPParen (Pat (HsPApp i (mkWildCards (length ts)))))]
                     in [HsMatch loc0  funNamePNT  pats (HsBody (Exp (HsId (HsCon (PNT (PN (UnQual "True")
                         (G (PlainModule "Prelude") "True" (N (Just loc0))))(Type blankTypeInfo) (N (Just loc0)))))))[]]
             match2 = if cons ==1 then []
                        else [HsMatch loc0 funNamePNT [Pat HsPWildCard] (HsBody (Exp (HsId (HsCon (PNT (PN 
                              (UnQual "False") (G (PlainModule "Prelude") "False" (N (Just loc0)))) (Type blankTypeInfo)
                              (N (Just loc0))))))) []]
             fun  = (Dec (HsFunBind loc0 (match1 ++ match2)))
         in ([typeSig, fun])
             
     mkWildCards 0 = []
     mkWildCards n = (Pat HsPWildCard) : mkWildCards (n-1)

-- collect the exisiting discriminators
existingDiscriminators mod (Dec (HsDataDecl _ c tp conDecls _))
    =filter (\x -> isJust (snd x)) $ map (findDiscriminator (hsModDecls mod)) conDecls
   where             
     findDiscriminator decls (conDecl:: HsConDeclP)  
       = let (dataCon,numOfFields)= case conDecl of 
                                       (HsRecDecl _ _ _ i ts) -> (pNTtoPN i, length ts)
                                       (HsConDecl _ _ _ i ts) -> (pNTtoPN i, length ts) 
             decls' = filter (\x -> isDiscriminator x (dataCon, numOfFields)) decls
         in if decls'==[] then (dataCon, Nothing)
                          else (dataCon, Just (ghead "findDiscriminator" (definedPNs (head decls'))))      
     isDiscriminator (Dec (HsFunBind _ (match1@(HsMatch _ _ [p] _ _):matches))) (dataCon,numOfFields) 
          = let conAndArity = getConAndArity p
            in if isJust conAndArity  
                  then let (con, arity) = fromJust conAndArity
                       in  (con, arity) == (dataCon, numOfFields)
                           && ((render.ppi) (rhsExp match1)) =="True" 
                           && (if matches==[] then True
                                 else length matches==1 && ((render.ppi) (rhsExp (head matches))) == "False")
                  else False  
          where      
             getConAndArity  (Pat (HsPApp i ps)) = Just ((pNTtoPN i), length ps)
             getConAndArity  (Pat (HsPId (HsCon i))) = Just ((pNTtoPN i),0)
             getConAndArity  (Pat (HsPParen p)) = getConAndArity p
             getConAndArity  (Pat (HsPAsPat i p)) = getConAndArity p
             getConAndArity  _  = Nothing
        
             rhsExp (HsMatch _ _ _ (HsBody e) _) = Just e
             rhsExp _ = Nothing

     isDiscriminator _  _ = False

----------------------------------------------------------------------------------------------
{- This refactoring adds constructor functions to a data type declaration.  The function names
   will be created by the refactorer automatically, however the user can rename them afterwards. 
   No pre-condition for this refactoring.
-}

addConstructors args
 =do let fileName= ghead "filename" args            
         row = read (args!!1)::Int
         col = read (args!!2)::Int   
     info@(_,_,mod,_) <- parseSourceFile fileName
     case checkCursor fileName row col mod of
       Left errMsg -> putStrLn errMsg
       Right decl  -> addConstructors' info decl fileName False 

addConstructors' (inscps,_, mod, toks)  decl fileName isSubRefactor
   = do clients <-clientModsAndFiles =<<RefacUtils.fileNameToModName fileName    
        clientInfo <- mapM parseSourceFile (map snd clients) 
        let inscpNames= map (\(x,_,_,_)->x) (concatMap inScopeInfo (inscps:(map (\(a,_,_,_)->a) clientInfo)))
        (mod',((toks',modified),_))<-runStateT (addConstructors'' inscpNames decl mod) ((toks, unmodified), (-1000,0))
        -- no need to modify the client modules, as the new name won't cause problems.
        writeRefactoredFiles isSubRefactor $ [((fileName,modified),(toks', mod'))]

         
addConstructors'' inscpNames decl@(Dec (HsDataDecl (SrcLoc  _ _ _ col) c tp conDecls _)) mod 
  = do let consWithConstrs = existingConstructors mod decl 
       if (length conDecls == length consWithConstrs) 
         then return mod -- all constructors already exist, so do nothing.
         else do let conDecls' = filter (\x->isNothing (find (conName' x==) (map fst consWithConstrs))) conDecls
                     funs =concatMap (mkConstructor col tp inscpNames mod) conDecls'
                 addDecl mod Nothing (funs,Nothing) True 
  where             
     mkConstructor startCol tp existingNames mod (decl@(HsRecDecl _ _ _ i ts):: HsConDeclP)
       = mkConstructor' startCol tp existingNames mod i (map (typeFromBangType.snd) ts)
     mkConstructor startCol tp existingNames mod (decl@(HsConDecl _ _ _ i ts):: HsConDeclP)
       = mkConstructor' startCol tp existingNames mod i (map typeFromBangType ts)
          
     mkConstructor' startCol tp existingNames mod i ts 
       = let funNamePNT =nameToPNT $ mkNewName (pNTtoName i) existingNames "mk" 0 
             numOfParams = length ts 
             typeSig = (Dec (HsTypeSig loc0 [funNamePNT] [] (mkTypeFun tp ts)))
             fun  = (Dec (HsFunBind loc0 [HsMatch loc0 funNamePNT [] (HsBody (Exp (HsId (HsCon i)))) []]))
          in ([typeSig, fun])
             
     mkTypeFun t ts = foldr (\ t1 t2 ->(Typ (HsTyFun t1 t2))) t ts

     typeFromBangType (HsBangedType t)   = t
     typeFromBangType (HsUnBangedType t) = t


--existingConstructors:: HsModuleP -> HsDeclP ->(PName, Maybe PName)
existingConstructors mod (Dec (HsDataDecl _ c tp conDecls _))
  =filter (\x -> isJust (snd x)) $ map (findConstructors (hsModDecls mod)) conDecls
  where             
    findConstructors decls (conDecl:: HsConDeclP)  
     = let (dataCon,numOfFields)= case conDecl of 
                                  (HsRecDecl _ _ _ i ts) -> (pNTtoPN i, length ts)
                                  (HsConDecl _ _ _ i ts) -> (pNTtoPN i, length ts) 
           decls' = filter (\x -> isConstructor x (dataCon, numOfFields)) decls
       in if decls'==[] then (dataCon, Nothing)
                        else (dataCon,  Just (ghead "findConstructors" (definedPNs (head decls'))))    
   
    isConstructor (Dec (HsFunBind _ [match1@(HsMatch _ _ ps (HsBody e) _ )])) (dataCon,numOfFields) 
      | length ps== numOfFields && all isVarPat ps 
       =hsPNs e ==dataCon : (hsPNs ps)       
    isConstructor (Dec (HsPatBind _  f (HsBody e) _)) (dataCon, numOfFileds)
       = (render.ppi) e == pNtoName dataCon
    isConstructor _ _ = False


--------------------Some utility functions --------------------------------------

-- check whether the cursor points to the beginning of the datatype declaration.
checkCursor::String->Int->Int->HsModuleP->Either String HsDeclP 
checkCursor fileName row col mod
  = case locToTypeDecl of
       Nothing   ->Left ("Invalid cursor position. Please place cursor at the beginning of the type constructor name!")
       Just decl ->Right decl                                
   where
    locToTypeDecl =find (definesTypeCon (locToPNT fileName (row,col) mod)) (hsModDecls mod)
   
    definesTypeCon pnt (Dec (HsDataDecl loc c tp _ _))= isTypeCon pnt && (findPNT pnt tp)
    definesTypeCon pnt _ = False 

-- Create a new name from the oldName, and the new name should not conflict with the exisiting names.
mkNewName oldName exisitingNames prefix init
  = let newName = if init==0 then prefix++oldName
                             else prefix++oldName++ show init
    in if elem newName exisitingNames
           then mkNewName oldName exisitingNames prefix (init+1)
           else newName


--get the list of free and declared variables.
existingVbls t = do (f,d)<-hsFDsFromInside t
                    return (f++d)

-- returns True if a pat is a variable.
isVarPat pat = case pat of
                  (Pat (HsPId (HsVar i))) -> True
                  (Pat (HsPAsPat i p))    -> isVarPat p
                  (Pat (HsPIrrPat p))     -> True
                  (Pat (HsPParen p))      -> isVarPat p 
                  (Pat (HsPWildCard))     -> True       
                  _                       -> False       

-- get the data constructor name.
conName (Dec (HsDataDecl _ _ _ cons _))
  = map conName' cons
conName _ = []

getCons (Dec (HsDataDecl _ _ _ cons _))
  = cons
getCons _ =[]

conName' (HsRecDecl _ _ _ i _) = pNTtoPN i
conName' (HsConDecl _ _ _ i _) = pNTtoPN i

conPNT (Dec (HsDataDecl _ _ _ cons _))
  = map conPNT' cons 
  where
    conPNT' (HsRecDecl _ _ _ i _) = i
    conPNT' (HsConDecl _ _ _ i _) = i
-- remove the enclosing parenthesis.
rmPParen p = case p of (Pat (HsPParen p')) -> rmPParen p'
                       _                   -> p
sNtoName (SN i _) = i     

pNtoVarEnt pn = EntE (Var (PNT pn Value (N (Just loc0))))

-- find the selector associated with the constructor name specified by 'conName' 
findSelectors conName allSelectors
  = let r = find (\(x,y)->x==conName) allSelectors 
    in if isNothing r  then error $ "Selectors do not exist for data constructor " ++ pNtoName conName
                       else (snd.fromJust) r
-- find the discriminator associated with the constructor name specified by `conName`
findDiscriminator conName allDiscrs
   = let r = find (\(x,y) -> x == conName) allDiscrs
     in if isNothing r then error $ "Discriminator does not exist for data constructor: " ++ pNtoName conName
                       else (snd.fromJust) r

--Collect all the field labels associated with the data declaration.
gatherSelectors::HsDeclP->[(PName,[String])]
gatherSelectors (Dec (HsDataDecl _ _ _ cons _))
  =map selectors cons
  where    -- data constructor decl with field labels
    selectors ((HsRecDecl _ _ _ i ts):: HsConDeclP)
      = (pNTtoPN i, map pNTtoName (concatMap fst ts))
    -- data constructors decl without field labels
    selectors ((HsConDecl _ _ _ i _)::HsConDeclP)
      = (pNTtoPN i, [])

--Collect all the discriminators associated with the data declaration in the current module.
gatherDiscriminators::HsDeclP->HsModuleP->[(PName,String)]
gatherDiscriminators decl mod 
  = map (\(x,y)->(x, pNtoName (fromJust y))) $ existingDiscriminators mod decl  

--Collect all the constructors associated with the data declatation in the current  module.
gatherConstructors::HsDeclP->HsModuleP->[(PName,String)]
gatherConstructors decl mod 
  = map (\(x,y) -> (x, pNtoName (fromJust y))) 
        $ filter (\(x,y)->isJust y) $ existingConstructors mod decl

resetVal = do  (t,(v,_)) <- get
               put (t, (v,0))

fakeTrueExp  =(Exp (HsId (HsCon (PNT (PN (UnQual "True") (G (PlainModule "Prelude") "True" (N (Just loc0))))
                   (Type blankTypeInfo) (N (Just loc0))))))

fakeTruePat=(Pat (HsPId (HsCon (PNT (PN (UnQual "True") (G (PlainModule "Prelude") "True" (N (Just loc0))))
                   (Type blankTypeInfo) (N (Just loc0))))))

fakeFalseExp =(Exp (HsId (HsCon (PNT (PN (UnQual "False") (G (PlainModule "Prelude") "False" (N (Just loc0))))
                   (Type blankTypeInfo) (N (Just loc0))))))
 

