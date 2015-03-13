
-- ++AZ++note: generaliseDef2is new since 0.6.0.2
module RefacGenDef(generaliseDef, generaliseDef2) where

import PrettyPrint
import PosSyntax
import Data.Maybe
import TypedIds
import UniqueNames
import PNT
import TiPNT
import Data.List
import RefacUtils
import Debug.Trace

{-A definition can be generialised by selecting a sub-expression of the RHS of the definition,
  and introducing that sub-expression as a new argument to the function/constant at each of its
  call sites. At the same time, a new formal parameter will be added to the generalised definition.

  When generalising a definition in a mutli-module context, there maybe several cases:
  1. The definition is not exported by the current module: refactoring only afftects this module.
  2. The definition is exported by the current module, but not used by any client modules.
  3. The definition is exported by the current module, and used any some client modules:
    2.1 The selected sub-expression does not contain any free variables.
    2.2 The selected sub-expression contains free variables. In this case, this is a possiblity that
        some of the free variables may not be visible in the client modules. These free variables might
        be from the current module, or from other modules that are imported by the current modules.One
        implementation option is to make these variables also visible to the client modules by modifying/
        adding import declarations. This involves chasing the origins of these free variables, and detecting
        possible name clashes/captures. Another implementation option is to define an auxiliary function
        to denote the sub-expression, and make this function visible to the client modules. We take the
        second option in our implementation. To ensure that the new function name does not cause name clash
        in the client modules, we take the visble names both in the current module and in the client modules
        into account when creating the new function name.
-}

-- ++AZ++ this function is new since 0.6.0.2
generaliseDef2 fileName newParamName beginPos endPos subExp inscps exps mod tokList
 = -- let fileName     = args!!0
   --    newParamName = args!!1
   --    beginPos     = (read (args!!2), read (args!!3))::(Int,Int)
   --    endPos       = (read (args!!4), read (args!!5)) :: (Int,Int)
   if isVarId newParamName -- the parameter name is a valid name.
      then do modName <- RefacUtils.fileNameToModName fileName
              -- (inscps,exps,mod, tokList) <- parseSourceFile fileName
              let pnt = findDefName tokList beginPos endPos  mod
                  pn           = pNTtoPN pnt
              if pn == defaultPN || subExp == defaultExp
                then error ("The highlighted source does not contain a rhs sub-expression, " ++
                       "or the selected sub-expression does not contain any identifiers so that the refactor could not locate it.")

                else if isExported pnt exps
                       then do clients <- clientModsAndFiles modName  -- returns [(module name ,filename)]
                               info    <- mapM parseSourceFile (map snd clients)   -- parse all the client modules
                               let funPName
                                    =if clients /= [] && hasFreeVars subExp  --THIS CONDITION MIGHT A LITTLE BIT LOOSE.
                                                                              --HOW ABOUT NONE OF THE CLIENTS USE IT?
                                        then let inscpNames =map (\ (x,_,_,_)->x) $ concatMap inScopeInfo (map myfst info) -- calculate all visibe names
                                             in  Just =<< mkNewFunPName pn (hsDecls mod) modName inscpNames
                                        else Nothing
                                   subExp' = if isJust funPName then pNtoExp (fromJust funPName) else subExp
                               (mod',((tokList',m),_)) <- doGeneralise True True pnt fileName subExp newParamName funPName mod tokList

                               refactoredClients   <- mapM (generaliseInClientMod True pnt subExp' modName funPName)
                                                       $ zip info (map snd clients)
                               -- writeRefactoredFiles False $ ((fileName,m), (tokList',mod')):refactoredClients
                               return (m, tokList', mod', refactoredClients)
                       else do (mod',((tokList',m),_))<-doGeneralise True True pnt fileName subExp newParamName Nothing mod tokList
                               -- writeRefactoredFiles False [((fileName,m), (tokList',mod'))]
                               return (m, tokList', mod', [])
      else error "Invalid parameter name!"



generaliseDef args
 = let fileName     = args!!0
       newParamName = args!!1
       beginPos     = (read (args!!2), read (args!!3))::(Int,Int)
       endPos       = (read (args!!4), read (args!!5)) :: (Int,Int)
   in if isVarId newParamName -- the parameter name is a valid name.
      then do modName <- RefacUtils.fileNameToModName fileName
              (inscps,exps,mod, tokList) <- parseSourceFile fileName
              let (pnt,subExp) = findDefNameAndExp tokList beginPos endPos  mod
                  pn           = pNTtoPN pnt
              if pn == defaultPN || subExp == defaultExp
                then error ("The highlighted source does not contain a rhs sub-expression, " ++
                       "or the selected sub-expression does not contain any identifiers so that the refactor could not locate it.")

                else if isExported pnt exps
                       then do clients <- clientModsAndFiles modName  -- returns [(module name ,filename)]
                               info    <- mapM parseSourceFile (map snd clients)   -- parse all the client modules
                               let funPName
                                    =if clients /= [] && hasFreeVars subExp  --THIS CONDITION MIGHT A LITTLE BIT LOOSE.
                                                                              --HOW ABOUT NONE OF THE CLIENTS USE IT?
                                        then let inscpNames =map (\ (x,_,_,_)->x) $ concatMap inScopeInfo (map myfst info) -- calculate all visibe names
                                             in  Just =<< mkNewFunPName pn (hsDecls mod) modName inscpNames
                                        else Nothing
                                   subExp' = if isJust funPName then pNtoExp (fromJust funPName) else subExp
                               (mod',((tokList',m),_)) <- doGeneralise False False pnt fileName subExp newParamName funPName mod tokList

                               refactoredClients   <- mapM (generaliseInClientMod False pnt subExp' modName funPName)
                                                       $ zip info (map snd clients)
                               writeRefactoredFiles False $ ((fileName,m), (tokList',mod')):refactoredClients
                       else do (mod',((tokList',m),_))<-doGeneralise False False pnt fileName subExp newParamName Nothing mod tokList
                               writeRefactoredFiles False [((fileName,m), (tokList',mod'))]
      else error "Invalid parameter name!"
--  where

   --find the definition name whose sub-expression has been selected, and the selected sub-expression.
findDefNameAndExp toks beginPos endPos t
    = fromMaybe (defaultPNT, defaultExp) (applyTU (once_tdTU (failTU `adhocTU` inMatch
                                                                     `adhocTU` inPat)) t)  --CAN NOT USE 'once_tdTU' here.

     where  --The selected sub-expression is in the rhs of a match
           inMatch (match@(HsMatch loc1  pnt pats rhs ds)::HsMatchP)
             | locToExp beginPos endPos toks rhs /= defaultExp

             = Just (pnt, locToExp beginPos endPos toks rhs)
           inMatch _ = Nothing

           --The selected sub-expression is in the rhs of a pattern-binding
           inPat (pat@(Dec (HsPatBind loc1 ps rhs ds))::HsDeclP)
             | locToExp beginPos endPos toks rhs /= defaultExp
             = if isSimplePatBind pat
                then Just (patToPNT ps, locToExp beginPos endPos toks rhs)
                else error "A complex pattern binding can not be generalised!"
           inPat _ = Nothing

findDefName toks beginPos endPos t
    = fromMaybe defaultPNT (applyTU (once_tdTU (failTU `adhocTU` inMatch
                                                                     `adhocTU` inPat)) t)  --CAN NOT USE 'once_tdTU' here.

     where  --The selected sub-expression is in the rhs of a match
           inMatch (match@(HsMatch loc1  pnt pats rhs ds)::HsMatchP)
             | locToExp beginPos endPos toks rhs /= defaultExp
               || locToPat beginPos endPos toks pats /= defaultPat
             = Just pnt
           inMatch _ = Nothing

           --The selected sub-expression is in the rhs of a pattern-binding
           inPat (pat@(Dec (HsPatBind loc1 ps rhs ds))::HsDeclP)
             | locToExp beginPos endPos toks rhs /= defaultExp
             = if isSimplePatBind pat
                then Just $ patToPNT ps
                else error "A complex pattern binding can not be generalised!"
           inPat _ = Nothing



   -- Do generalisation in current module.
doGeneralise recursive flag pnt@(PNT pn _ _)  fileName subExp newParamName newFunPName mod tokList
     = runStateT (if isJust newFunPName
                    then do -- add the new function name to the export list
                            mod'<-addItemsToExport mod (Just pn) False (Left [pNtoName (fromJust newFunPName)])
                            doGeneralise' mod'
                    else doGeneralise' mod) ((tokList,unmodified),(-1000,0))
      where

      doGeneralise' mod
         = applyTP (once_tdTP (failTP `adhocTP` inMod
                                      `adhocTP` inMatch
                                      `adhocTP` inPat
                                      `adhocTP` inLet
                                      `adhocTP` inAlt
                                      `adhocTP` inStmt) `choiceTP` failure) mod
        where

           --1.pn is declared in top level
           inMod (mod@(HsModule loc name exps imps ds):: HsModuleP)
               | definingDecls [pn] ds False False/=[]
              = do worker pnt subExp newParamName mod ds newFunPName
           inMod _ =mzero

           --2. pn is declared locally in the where clause of a match.
           inMatch (match@(HsMatch loc1 name pats rhs ds)::HsMatchP)
               | definingDecls [pn] ds False  False/=[]
              = worker pnt subExp newParamName match ds newFunPName
           inMatch _ =mzero

           --3. pn is declared locally in the where clause of a pattern binding.
           inPat (pat@(Dec (HsPatBind loc p rhs ds))::HsDeclP)
               | definingDecls [pn] ds False  False /=[]
              =  worker pnt subExp newParamName pat ds newFunPName
           inPat _=mzero

           --4: pn is declared locally in a  Let expression
           inLet (letExp@(Exp (HsLet ds e))::HsExpP)
               | definingDecls [pn] ds False  False /=[]
               = worker pnt subExp newParamName letExp ds newFunPName
           inLet _=mzero

           --5. pn is declared locally in a  case alternative.
           inAlt (alt@(HsAlt loc p rhs ds)::HsAltP)
               | definingDecls [pn] ds False  False/=[]
               = worker pnt subExp newParamName alt ds newFunPName
           inAlt _=mzero

            --6.pn is declared locally in a let statement.
           inStmt (letStmt@(HsLetStmt ds stmts):: HsStmtP)
               | definingDecls [pn] ds False  False/=[]
             = worker pnt subExp newParamName letStmt ds newFunPName
           inStmt _=mzero

           failure=idTP `adhocTP` mod
               where mod (m::HsModuleP)=error "Refactoring failed"


      worker pnt@(PNT pn _ _) subExp newParamName parent ds newFunPName
       = do --add formal parameter to the generalised function
           let newParamPName = nameToPN newParamName
               declToBeGeneralised = definingDecls [pn] ds False False
           doChecking declToBeGeneralised
           parent' <- if isJust newFunPName
                       then do let declToAdd=Dec (HsPatBind loc0 (pNtoPat (fromJust newFunPName)) (HsBody subExp) [])
                               addDecl parent (Just pn) ([declToAdd],Nothing) True
                       else return parent
           ds''<-replaceExpByParam pn subExp newParamPName =<<commentOutTypeSig pn (hsDecls parent')
           ds'''<-addParamsToDecls ds'' pn [newParamPName] True

           --ds''<- addFormalParam pn subExp newParamName =<<commentOutTypeSig pn ds'
           --Check clashed names because of the adding of subExp as a actual parameter.
           parent''<- renamingCheck pn subExp $ replaceDecls parent' ds'''
           --Adding the actual parameter to each call site of the generalised function name.
           addActualArg recursive pn subExp parent''
        where
         doChecking decl
          | flag == False
              = do (expFreeVars,_) <- hsFreeAndDeclaredPNs subExp
                   (defFreeVars,_) <- hsFreeAndDeclaredPNs decl
                   if expFreeVars \\ defFreeVars /= []
                     then do error "The selected expression should not contain locally declared variables!"
                     else do (f,d) <- hsFDsFromInside =<<  replaceExpByDefault subExp decl
                             d'   <- hsVisiblePNs  subExp decl
                             if elem newParamName $ map pNtoName (f `union` d `union` d')
                               then error "The parameter name will cause name clash or semantics change, please choose another name!"
                               else return ()
          | otherwise = do  (f,d) <- hsFDNamesFromInside decl
                            if elem newParamName (f ++ d)
                               then error "The parameter name will cause name clash or semantics change, please choose another name!"
                               else return ()

         {- substitute the occurrence of an expression by the default expression,
            in order to get rid of the free variables in the generalised sub-expression -}
         replaceExpByDefault e = applyTP (once_tdTP (failTP `adhocTP` inExp))
          where
             --only replace the higelighted expression
            inExp (e1::HsExpP)
             |sameOccurrence e1 e
              = return defaultExp
            inExp x = mzero

         --Replace occurrence of the highlighted expression by the formal parameter.
         replaceExpByParam pn e paramPName = applyTP (once_tdTP (failTP `adhocTP` inDecl))
          where
            --The sub-expression is in the rhs of a function definition.
           inDecl (fun@(Dec (HsFunBind _  ((HsMatch _ (PNT pname _ _) _ _ _):ms)))::HsDeclP)
             | pn == pname
              = replaceExpByParam' fun
            --The sub-expression is in the rhs of a pattern binding
           inDecl (pat@(Dec (HsPatBind loc1 ps rhs ds))::HsDeclP)
             | pn == patToPN  ps
              = replaceExpByParam' pat
           inDecl _ =mzero

           replaceExpByParam'= applyTP (stop_tdTP (failTP `adhocTP` inExp))  -- use once_td to only replace the
                                                                                       -- highlighted occurrence.
             where
              inExp (e1 ::HsExpP)
                | e1 == e  -- && srcLocs e == srcLocs e1   --ONLY REPLACE THE HIGHLIGHTED EXP.
                = do let newExp=pNtoExp paramPName
                     update e1 newExp e1

              inExp e = mzero

         renamingCheck pn subExp parent
          = do --free variables declared in the highlighted expression
               (f,_) <- hsFreeAndDeclaredPNs subExp
                --visible variables to the generalised function name in its use places.
               vVars <- hsVisiblePNs pn parent
               --clasedNames names come  from the vVars
               let clashedNames = filter (\x->elem (pNtoName x) (map pNtoName f)) $  (nub vVars \\ nub f)
               if clashedNames == []
                 then return parent
                 else error ("The identifier(s):" ++ showEntities showPNwithLoc clashedNames ++
                          " will cause name capture/clash after generalisation, please do renaming first!")

      {- if the generalised declaration is a direct recursion function, then add the parameter
         as the actual argument; otherwise add the highlighted expression as a actual paramter
         to the generalised function at each of its call sites -}

addActualArg recursion pn subExp
        = if recursion then applyTP (stop_tdTP (failTP `adhocTP` funApp))
                       else applyTP (stop_tdTP (failTP `adhocTP` inDecl
                                                       `adhocTP` funApp))
       where
         inDecl (fun@(Dec (HsFunBind _  ((HsMatch _ (PNT pname _ _) _ _ _):ms)))::HsDeclP)
           | pn == pname
           = return fun

         inDecl (pat@(Dec (HsPatBind loc1 ps rhs ds))::HsDeclP)
           | pn == patToPN  ps
           = return pat
         inDecl _ = mzero

         funApp (Exp (HsApp e  exp@(Exp (HsId (HsVar pnt@(PNT pname _ _ )))))::HsExpP)
           | pname == pn --ganrantee this is a use place of pn
          = do exp'<-doAddingActulaArg pnt exp subExp True
               return (Exp (HsApp e  exp'))

         funApp (exp@(Exp (HsId (HsVar pnt@(PNT pname _ _))))::HsExpP)
           | pname == pn  --ganrantee this is a use place of pn
          = doAddingActulaArg pnt exp subExp False

         funApp _ = mzero

doAddingActulaArg pnt pntExp subExp addParen
     = do let newExp = if isSimpleExp subExp || isParenExp subExp
                         then if addParen then (Exp (HsParen (Exp (HsApp pntExp subExp))))
                                          else (Exp (HsApp pntExp subExp))
                         else if addParen then (Exp (HsParen (Exp (HsApp pntExp (Exp (HsParen subExp))))))
                                          else (Exp (HsApp pntExp (Exp (HsParen subExp))))
          update pntExp newExp pntExp

     where


       isSimpleExp (Exp (HsId _))=True
       isSimpleExp (Exp (HsLit _ _))=True
       isSimpleExp _ =False

       isParenExp (Exp (HsParen _))=True
       isParenExp _=False

addActualArgInClientMod pn qual funName toBeQualified t
      = applyTP (stop_tdTP (failTP `adhocTP`funApp)) t
       where
         funApp (Exp (HsApp e  exp@(Exp (HsId (HsVar pnt@(PNT pname _ _ )))))::HsExpP)
           | pname == pn --ganrantee this is a use place of pn
          = do vs <- hsVisibleNames pnt t
               let e'=if toBeQualified || elem (pNtoName funName) vs
                        then pNtoExp (qualifyPName qual funName)
                        else pNtoExp funName
               exp'<- doAddingActulaArg pnt exp  e' True
               return (Exp (HsApp e  exp'))

         funApp (exp@(Exp (HsId (HsVar pnt@(PNT pname _ _))))::HsExpP)
           | pname == pn  --ganrantee this is a use place of pn
          = do vs <- hsVisibleNames pnt t
               let e'=if toBeQualified || elem (pNtoName funName) vs
                        then pNtoExp (qualifyPName qual funName)
                        else pNtoExp funName
               doAddingActulaArg pnt exp e' False

         funApp _ = mzero

generaliseInClientMod recursive pnt subExp serverModName newFunPName ((inscps, exps, mod,ts) ,fileName)
      = let qual  = hsQualifier  pnt inscps
            pn    = pNTtoPN pnt
        in if qual==[]
            then --This name is not imported
                 return ((fileName,unmodified), (ts,mod))
            else do (mod',((ts',m), _))
                       <- runStateT (if isNothing newFunPName
                                       then addActualArg recursive pn subExp mod
                                       else do let funName=fromJust newFunPName
                                               mod' <- addItemsToImport serverModName (Just pn) (Left [pNtoName funName]) mod
                                               mod''<- addItemsToExport mod' (Just pn) False (Left [pNtoName funName])
                                               if isInScopeAndUnqualified (pNtoName pn) inscps
                                                 then addActualArgInClientMod pn  (head qual) funName False mod''
                                                 else addActualArgInClientMod pn  (head qual) funName True mod'')
                                     ((ts,unmodified), (-1000,0))
                    return ((fileName,m),(ts',mod'))

myfst (a,_,_,_) = a

{- Create the auxiliary function name. Suppose the original function name is 'f',
   then the auxiliary function name is like 'f_gen_i', where i is an integer. -}
mkNewFunPName pn e modName inscopeNames
   =do  (f1,d1) <- hsFDsFromInside e
        let name=mkNewName ((pNtoName pn)++"_gen") (nub ((map pNtoName (f1 `union` d1)) `union` inscopeNames)) 0
        return (PN (UnQual name) (G modName name (N (Just loc0))))
