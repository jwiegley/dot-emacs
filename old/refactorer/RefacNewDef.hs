

module RefacNewDef(introNewDef,unfoldDef,doUnfolding1) where

import PrettyPrint
import PosSyntax
import Data.Maybe
import TypedIds
import UniqueNames hiding (srcLoc)
import PNT 
import TiPNT 
import Data.List  
import RefacUtils
import PFE0 (findFile)
import MUtils(( # ))
import AbstractIO
--Introdule a new defintion whose rhs is the user specified expression
introNewDef args
 = do let fileName   = args!!0
          newFunName = args!!1            
          beginRow   = read (args!!2)::Int
          beginCol   = read (args!!3)::Int
          endRow     = read (args!!4)::Int
          endCol     = read (args!!5)::Int
      modName <- fileNameToModName fileName 
      if isVarId newFunName then
         do (inscps, exps, mod, tokList) <- parseSourceFile fileName  
            let exp = locToExp (beginRow,beginCol) (endRow, endCol) tokList mod 
            (mod',((tokList',m),_))<-doIntroduce fileName newFunName (beginRow,beginCol)(endRow,endCol) mod tokList           
            writeRefactoredFiles False [((fileName,m), (tokList',mod'))]
         else error "Invalid new function name!"

  where
   ---Introduce the new defintion, and put it at the end of next lower level declaration list
   doIntroduce fileName newFunName beginPos endPos mod tokList 
      =runStateT (applyTP (once_buTP (failTP `adhocTP` inMatch
                                             `adhocTP` inPat
                                             `adhocTP` inLetExp
                                             `adhocTP` inAlt
                                             `adhocTP` inStmt) `choiceTP` failure) mod) 
                         ((tokList,unmodified), (-1000,0))
                         
        where
           --The sub-expression is in the rhs of a match
           inMatch (match@(HsMatch loc1 name pats rhs ds)::HsMatchP)
              | inRegion rhs tokList beginPos endPos && locToExp beginPos endPos tokList rhs /= defaultExp 
                  =doIntroduce' match  rhsIn  replaceRhs                 
           inMatch _ =mzero
           
           --The sub-expression is in the rhs of a pattern binding
           inPat (pat@(Dec (HsPatBind loc1 ps rhs ds))::HsDeclP)
              | inRegion rhs tokList beginPos endPos && locToExp beginPos endPos tokList rhs /= defaultExp
                     =doIntroduce' pat  rhsIn   replaceRhs   
           inPat _ =mzero
 
           -- The sub-expression is in the expression of a 'Let ... in'      
           inLetExp (exp@(Exp (HsLet ds e))::HsExpP)
               | inRegion e tokList beginPos endPos && locToExp beginPos endPos tokList e /= defaultExp
                    =doIntroduce'' exp expIn  replaceExpInLet 
           inLetExp _=mzero
                
           -- The sub-expression is in the rhs of a case alternative
           inAlt (alt@(HsAlt loc p rhs ds)::HsAltP)
                | inRegion rhs tokList beginPos endPos &&  locToExp beginPos endPos tokList rhs /= defaultExp
                    =doIntroduce' alt  rhsIn replaceRhs  
           inAlt _=mzero
      
                 -- The sub-expression is in the stmts of a 'let'    
           inStmt (stmt@(HsLetStmt ds stmts):: HsStmtP)
                | inRegion stmts tokList beginPos endPos &&  locToExp beginPos endPos tokList stmts /= defaultExp
                     =doIntroduce'' stmt  stmtsIn replaceStmtsInDo  
           inStmt  _=mzero

           failure=idTP `adhocTP` mod
                 where mod (m::HsModuleP)=error "The highlighted source does not contain a sub-expression!"          

           --ORDER MATTERS HERE
           doIntroduce' parent getRhs replaceFun 
               =do
                   (f,d)<-hsFDsFromInside parent		  
                   if elem newFunName (map pNtoName (f `union` d))
                      then 
                         error "The new function name would cause name clash/capture, please select another name!"
                      else
                         do 
                            let exp=locToExp beginPos endPos tokList (getRhs parent) 
                            (freeVars,declVars)<-hsFreeAndDeclaredPNs exp        
                            let 
                                params=(freeVars \\ (nub (f `union` d)))  --get parameters to the new function. 
                                --params = freeVars `intersect` d 
                                (newFun,newFunPName)=mkNewFun  newFunName params exp
                            parent'<-addDecl parent Nothing ([newFun], Nothing) False
                            --unified foldOneExp and foldAllExps to foldExps, 
                            --then switched back to 1, see comment for foldExps -- Claus
                            --1: only fold the highlighted expression
                            --rhs'<-foldExps False exp newFunPName params (fromJust(getRhs parent))
                            --2: fold all the courrences of the same expression
                            rhs'<-foldExps True exp newFunPName params (fromJust(getRhs parent))   
                            return (replaceDecls (replaceFun parent rhs') (hsDecls parent'))
                            --return (replaceDecls parent (hsDecls parent ++ [newFun])) 
                            --3: without folding expression:
                            -- return (replaceDecls parent (newFun:(hsDecls parent)))
           --ORDER MATTERS HERE.
           doIntroduce'' parent getRhs replaceFun  
               =do (f,d)<-hsFDsFromInside parent
                   if elem newFunName (map pNtoName (f `union` d))
                      then 
                         error "The new function name would cause name clash/capture, please select another name!"
                      else
                         do let exp=locToExp beginPos endPos tokList (getRhs parent)
			      
                            (freeVars,_)<-hsFreeAndDeclaredPNs exp
                            let 
                                params=(freeVars \\ (nub (f `union` d)))  --get parameters to the new function. 
                                (newFun,newFunPName)=mkNewFun newFunName params exp
                            --unified foldOneExp and foldAllExps to foldExps, 
                            --then switched back to 1, see comment for foldExps -- Claus
                            --1: only fold the highlighted expression
                            --rhs'<-foldExps False exp newFunPName params (fromJust(getRhs parent))
                            --2: fold all the courrences of the same expression
                            rhs'<-foldExps True exp newFunPName params (fromJust(getRhs parent))
                            parent'<-addDecl parent Nothing ([newFun], Nothing) False
                            return (replaceDecls (replaceFun parent rhs') (hsDecls parent'))
                            --return (replaceDecls parent (hsDecls parent ++ [newFun])) 
                            --3: without folding expression:
                            -- return (replaceDecls parent (newFun:(hsDecls parent)))

           mkNewFun funName params e
             =let funPName= PN (UnQual funName) (S loc0)
                  funDecl = Dec (HsFunBind loc0 [HsMatch loc0 (PNT funPName Value (N (Just loc0)))
                           (map pNtoPat  params) (HsBody e) []])
                 --ATTENTION: if length[params]=0, SHOULD CREATE AN PATTERN BINDING.
                 --mkLocsUnique should apply here becaue the location of params need to change.
                 --funDecl'<-mkLocsUnique funDecl [(pNtoLoc funPName)]
              in (funDecl, funPName) 

         
   -- won't work for all==True! for identifiers, == looks *only* at the location,
   -- so after setting all locations to some default with rmLocs,
   -- *all* identifiers look equal 
   foldExps all e funPName paramPNames
       =applyTP (traversal (failTP `adhocTP` exp))  --use once_tdTP if only fold one expression.                     
         where
            traversal   :: MonadPlus m => TP m -> TP m
            traversal    = if all then stop_tdTP else once_tdTP
            compare     :: (Eq t ,Term t) => t -> t -> Bool
            compare e1 e = if all 
                            then toRelativeLocs e1 == toRelativeLocs e
                            --then e1==e --does not handle the cases like [\x->x, \x->x].
                            else sameOccurrence e1 e
            exp (e1 ::HsExpP)
               | compare e1 e =  do let funExp=pNtoExp funPName
                                        paramExps=map pNtoExp paramPNames
                                        newExp = foldl addParamToExp funExp paramExps
                                    update e1 newExp e1                                         
            exp (e1@(Exp (HsDo stmts))::HsExpP)
              |isDoExp e
              =do let atoms=doExp2StmtList e 
                      atoms1 =getStmtList stmts                 
                  if atoms `intersect` atoms1 ==[]
                   then fail "Expession not found"
                   else do let (atoms11,atoms12) = break (== (ghead "foldExps" atoms)) atoms1
                               atoms12'=atoms12 \\ atoms 
                               funExp=pNtoExp funPName
                               paramExps=map pNtoExp paramPNames
                               newExp' = (HsQualifierAtom (foldl addParamToExp funExp paramExps))
                           newStmts'<-atoms2Stmt (atoms11++[newExp'] ++ atoms12')                          
                           let newExp = Exp (HsDo newStmts')
                           (f,d)<-hsFreeAndDeclaredPNs newExp
                           (_,d1)<-hsFreeAndDeclaredPNs e
                           let vs= f `intersect` d1
                           if vs /= [] 
                             then error ("The declared variable(s): " ++ showEntities (render.ppi) vs
                                         ++", is(are) used outside the selected statements.")
                             else update e1 newExp e1   
            exp _ =mzero
            
            --Add a parameter to an expression
            addParamToExp  e param=(Exp (HsApp e param)) 

            doExp2StmtList (Exp (HsDo stmts)) = getStmtList stmts
            doExp2StmtList _ = []

            isDoExp (Exp (HsDo _)) = True
            isDoExp _ = False
 

            getStmtList (HsGenerator l p e s) = HsGeneratorAtom l p e : getStmtList s
            getStmtList (HsQualifier e s)   = HsQualifierAtom e : getStmtList s
            getStmtList (HsLetStmt ds s)    = HsLetStmtAtom ds : getStmtList s
            getStmtList (HsLast e)          = [HsQualifierAtom e]

            atoms2Stmt [HsQualifierAtom e]          = return (HsLast e)
            atoms2Stmt [HsLastAtom e]               = return (HsLast e)
            atoms2Stmt (HsGeneratorAtom s p e : ss) = HsGenerator s p e # atoms2Stmt ss
            atoms2Stmt (HsLetStmtAtom ds : ss)      = HsLetStmt ds # atoms2Stmt ss
            atoms2Stmt (HsQualifierAtom e : ss)     = HsQualifier e # atoms2Stmt ss
            atoms2Stmt _ = fail "last statement in a 'do' expression must be an expression"

   foldAllExps e funPName paramPNames
       =applyTP (stop_tdTP (failTP `adhocTP` exp))  --use once_tdTP if only fold one expression.                     
         where
            exp (e1 ::HsExpP)
               | rmLocs e1==e
              =do let funExp=pNtoExp funPName
                      paramExps=map pNtoExp paramPNames
                      newExp = foldl addParamToExp funExp paramExps
                  update e1 newExp e1           
            exp _ =mzero
            --Add a parameter to an expression
            addParamToExp  e param=(Exp (HsApp e param)) 


class (Term t) =>RhsIn t where
  
    rhsIn:: t->Maybe RhsP

instance RhsIn HsMatchP where   
    rhsIn (HsMatch loc1 fun pats rhs ds)=Just rhs
           
instance RhsIn  HsDeclP where
    rhsIn (Dec (HsPatBind loc p rhs ds))=Just rhs                
    rhsIn _ =Nothing

instance RhsIn HsModuleP where
    rhsIn mod=Nothing

instance RhsIn HsAltP where
    rhsIn (HsAlt loc p rhs ds)=Just rhs

expIn ((Exp (HsLet ds exp))::HsExpP)=Just exp
expIn _=Nothing 

stmtsIn ((HsLetStmt ds stmts):: HsStmtP)=Just stmts
stmtsIn _=Nothing

------------------------------End of introducing a new definition-------------------------------------

{-ufolding a definition replaces a function call by its definition, the unfolded definition should be 
 a function/simple pattern binding. -}

unfoldDef args
 =do let fileName = ghead "fileName'" args 
         row      = read (args!!1)::Int
         col      = read (args!!2)::Int 
     modName <-fileNameToModName fileName
     (inscps, exps, mod, tokList)<-parseSourceFile fileName
     let pnt = locToPNT fileName (row, col) mod
         pn  = pNTtoPN pnt                           
     if pn /=defaultPN  && (defineLoc pnt /= useLoc pnt)
       then 
         do decl<-findDefiningDecl pn modName mod
            if decl/=[] 
              then do unInscopeIds <- freeVarsNotInScope decl inscps pnt mod 
                      if unInscopeIds == [] 
                        then do (mod',((tokList',m),_))<-runStateT (doUnfolding pnt (ghead "unfoldDef" decl) mod)
                                                          ((tokList,unmodified), (-1000,0))
                                writeRefactoredFiles False [((fileName,m), (tokList',mod'))]
                        else showNotInScopeError unInscopeIds  
              else error "Selected identifer is not a function/pattern binding name!"  
       else error "\nInvalid cursor position!\n"
 
   where 
         
    findDefiningDecl  pn currentModName currentMod
      = let defineModName=hasModName pn
        in if isLocalPN pn || defineModName == Just currentModName
             then return $ definingDecls [pn] (hsModDecls currentMod) False True
             else do (inscps, exps, mod, tokList)<-parseSourceFile =<<PFE0.findFile (fromJust defineModName)
                     return $ definingDecls [pn] (hsModDecls mod) False True

    freeVarsNotInScope unfoldedDecl inscps pnt mod
       = do (f,_)<-hsFreeAndDeclaredPNs unfoldedDecl 
            dl<-hsVisiblePNs pnt mod         
            let freePnts=filter (\x->elem (pNTtoPN x) f) $ hsPNTs unfoldedDecl
                freePnts'=filter (\x-> not (elem (pNTtoPN x) dl)) freePnts
            return $ nub.(map pNTtoPN) $ filter (\x -> hsQualifier x inscps == []) freePnts'


    showNotInScopeError unInscopeIds 
       = if length unInscopeIds>1        
            then error ("The free identifiers:" ++ showEntities pNtoQuotedName unInscopeIds ++
                        ", used in the definition to be unfolded, are not in scope in the current module!")
            else error ("The free identifier:" ++ showEntities pNtoQuotedName unInscopeIds ++
                        ", used in the definition to be unfolded, is not in scope in the current module!")
        where
          pNtoQuotedName pn =" '"++pNtoName pn++"'" 

                           
    doUnfolding pnt unfoldedDecl mod 
      =do simplifiedDecl<-simplifyDecl unfoldedDecl
          --simplifiedDecl <-mkLocsUnique simplifiedDecl' []
          doUnfolding' pnt simplifiedDecl mod 
      where 

        doUnfolding' pnt simplifiedDecl mod
           =applyTP (once_tdTP (failTP `adhocTP` inMatch
                                       `adhocTP` inPat) `choiceTP` failure) mod 
          where
            inMatch (match@(HsMatch loc1 name pats rhs ds)::HsMatchP)
              |findEntity pnt rhs 
                = do match'<-renameInAppSite pnt simplifiedDecl match
                     doUnfolding'' pnt  simplifiedDecl  match'
            inMatch _ =mzero
     
            inPat (pat@(Dec (HsPatBind loc p rhs ds))::HsDeclP)
              |findEntity pnt rhs 
                =do pat'<-renameInAppSite pnt simplifiedDecl pat
                    doUnfolding'' pnt simplifiedDecl pat'                   
            inPat _=mzero
          
            failure=idTP `adhocTP` mod
                where mod (m::HsModuleP)=error "Refactoring failed!"  
          
            renameInAppSite pnt unfoldedDecl t
             =do (f,_)<-hsFreeAndDeclaredPNs unfoldedDecl 
                 dl<-hsVisiblePNs pnt t
                 --'f\\dl' is used to handle in case that the unfoldedDecl is a local decl of the parent.
                 --see 'ComplexPatIn1.hs' for an example.
                 let clashedNames=filter (\x-> elem (pNtoName x) (map pNtoName (f\\dl))) (nub dl) 
                 t'<-foldM (flip (autoRenameLocalVar True)) t clashedNames  
                 return t'
               
            renameInUnfoldedDecl unfoldedDecl subst@(pn, exp) --pn is the formal parameter, exp is the actual parameter.
              =do  ds<-hsVisiblePNs pn unfoldedDecl
                   (f,_)<-hsFreeAndDeclaredPNs exp
                   let clashedNames=filter (\x->elem (pNtoName x) (map pNtoName f)) (nub ds)
                   foldM (flip (autoRenameLocalVar False)) unfoldedDecl clashedNames

            doUnfolding'' pnt unfoldedDecl 
              =applyTP (once_tdTP (failTP `adhocTP` exp)) 
                where
                  exp (e::HsExpP) --Because of the once_td traversal, the 'e' here must be the whole rhs or guard expression.
                    |findPNT pnt e
                    =if isComplexPatBind unfoldedDecl
                        then do replacePatCallByExp pnt unfoldedDecl e
                        else do let formalParams=paramsInDecl unfoldedDecl --get formalParams in unfolded declaration.
                                    actualParams=allParams pnt e     --get actual parameters.
                                    subst=zipWith (,) (map patToPN  formalParams) actualParams                         
                                unfoldedDecl'<-foldM  renameInUnfoldedDecl unfoldedDecl subst
                                --some formal parameters may have been renamed.
                                let formalParams'=paramsInDecl unfoldedDecl' 
                                    subst'=zipWith (,) (map patToPN formalParams') actualParams
                                    extraFormalParams=drop (length actualParams) formalParams'
                                decl'<-foldM replaceExp unfoldedDecl' subst'  -- why not modify the token stream?
                                let rhsExp=if extraFormalParams/=[]  --In case of partial application, convert extra
                                                                   --formal parameters into lambda exprssion.
                                        then (Exp (HsLambda extraFormalParams (fromJust (rhsExpInDecl decl'))))
                                        else fromJust (rhsExpInDecl decl')
                                    localDecls=hsDecls decl'
                                replaceFunCallByExp pnt rhsExp localDecls =<<(rmParams pnt (length subst')) e 
                  exp _=mzero
          
       
     --a pattern binding is a complex if the pattern is not a single variable.
    isComplexPatBind decl=case decl of
                   Dec (HsPatBind _ p _ _)->patToPN p ==defaultPN
                   _ ->False

    replacePatCallByExp pnt decl
     =applyTP (full_buTP (idTP `adhocTP` worker))
        where worker (e::HsExpP)
                | sameOccurrence (expToPNT e) pnt   --in 'sameOccurrence', use location matters.
                     =do let newExp=Exp (HsParen (Exp (HsLet [decl] e))) 
                         update e newExp e                     
              worker x =return x

 
       
    ---replace the function name by its definition
    replaceFunCallByExp pnt exp localDecls
      = applyTP (full_buTP (idTP `adhocTP` worker)) 
         where worker (e::HsExpP)
                 |sameOccurrence (expToPNT e) pnt
                     =do let newExp=if localDecls/=[]
                                     then Exp (HsParen (Exp (HsLet localDecls exp)))
                                     else Exp (HsParen exp)  --Should check if exp is already a Hsparen expression!
                         update e newExp e                             
               worker x=return x
   

    --get the parameters in the declaration (there should be only once match).
    paramsInDecl decl = case decl of
                     (Dec (HsFunBind _ ((HsMatch _  _ pats _ _):_))) ->pats
                     _ ->[]
 
    --get the right hand side repression in a declaration
    rhsExpInDecl (Dec (HsFunBind _ ((HsMatch _ _  _ (HsBody e) _):_)))=Just e 
    rhsExpInDecl (Dec (HsPatBind _ _ (HsBody e) _))=Just e

    --get all the parameters to pnt (which is a function name) in expression 'exp'
    allParams pnt exp=allParams' pnt exp []
        where allParams' pnt exp initial -- pnt:function/pattern name.
                 =let p=getOneParam pnt exp
                  in if p/=defaultExp  then allParams' pnt (rmOneParam pnt exp) (initial++[p])         
                                       else initial

    --get the first parameter of pnt
    getOneParam pnt t
       =fromMaybe defaultExp (applyTU (once_tdTU (failTU `adhocTU` worker)) t)
         where
           worker (Exp (HsApp e1 e2))
              |sameOccurrence (expToPNT e1) pnt=Just e2
           worker _ =Nothing

    --remove the first parameter of pnt
    rmOneParam  pnt t
        =fromMaybe defaultExp (applyTP (stop_tdTP (failTP `adhocTP` worker)) t)
           where
             worker (Exp (HsApp e1 e2 ))
               |sameOccurrence (expToPNT e1) pnt =Just e1
             worker _=Nothing

--substitute an old expression by new expression
replaceExp decls subst
    = applyTP (full_buTP (idTP `adhocTP` worker)) decls
           where worker (e::HsExpP)
                   |(expToPN e/=defaultPN) &&  (expToPN e) == (fst subst) 
                       && pNtoName (expToPN e) == pNtoName (fst subst)
                       =return (snd subst)
                 worker x=return x 


--Replace the old rhs by a new one---- 
class (Term t) => ReplaceRhs t where
  
    replaceRhs:: t->RhsP->t

instance ReplaceRhs HsMatchP where   
    replaceRhs (HsMatch loc1 fun pats rhs ds) rhs'
                 =(HsMatch loc1 fun pats rhs' ds)
           
instance ReplaceRhs HsDeclP where
    replaceRhs (Dec (HsPatBind loc p rhs ds)) rhs'
                =Dec (HsPatBind loc p rhs' ds)
    replaceRhs x _ =x
         
instance ReplaceRhs HsAltP where
    replaceRhs (HsAlt loc p rhs ds) rhs'
                 =HsAlt loc p rhs' ds


replaceExpInLet (Exp (HsLet ds e)) e'=(Exp (HsLet ds e'))
replaceExpInLet x _=x 

replaceStmtsInDo (HsLetStmt ds stmts) stmts'=HsLetStmt ds stmts'
replaceStmtsInDo x _=x


-----------------------------End of unfolding --------------------------------------------

----------------------Following code does not belong to any refactorings yet------------------


doUnfolding1 pn unfoldedDecl mod 
      =do simplifiedDecl<-simplifyDecl unfoldedDecl
          --simplifiedDecl <-mkLocsUnique simplifiedDecl' []
          doUnfolding' pn simplifiedDecl mod 
      where 

        doUnfolding' pn  simplifiedDecl mod
           =applyTP (full_tdTP (idTP `adhocTP` inMatch
                                     `adhocTP` inPat) `choiceTP` failure) mod 
          where
            inMatch (match@(HsMatch loc1 name pats rhs ds)::HsMatchP)
              |findPN pn rhs 
                = do match'<-renameInAppSite pn simplifiedDecl match
                     let pnts = hsPNTs pn match'
                     foldM (doUnfolding' simplifiedDecl) match' pnts
            inMatch _ =mzero
     
            inPat (pat@(Dec (HsPatBind loc p rhs ds))::HsDeclP)
              |findPN pn rhs 
                =do pat'<-renameInAppSite pn simplifiedDecl pat
                    let pnts = hsPNTs pn pat' 
                    foldM (doUnfolding' simplifiedDecl) pat' pnts 
            inPat _=mzero
          
            failure=idTP `adhocTP` mod
                where mod (m::HsModuleP)=error "Refactoring failed!"  
          
            hsPNTs pn =(nub.ghead "hsPNTs").applyTU (full_tdTU (constTU [] `adhocTU` inPnt))
               where
                 inPnt pnt@(PNT pn1  _ _)
                   |pn1 == pn 
                   =return [pnt]

            renameInAppSite pn unfoldedDecl t
             =do (f,_)<-hsFreeAndDeclaredPNs unfoldedDecl 
                 dl<-hsVisiblePNs pn t
                 --'f\\dl' is used to handle in case that the unfoldedDecl is a local decl of the parent.
                 --see 'ComplexPatIn1.hs' for an example.
                 let clashedNames=filter (\x-> elem (pNtoName x) (map pNtoName (f\\dl))) (nub dl) 
                 t'<-foldM (flip (autoRenameLocalVar True)) t clashedNames  
                 return t'
               
            renameInUnfoldedDecl unfoldedDecl subst@(pn, exp) --pn is the formal parameter, exp is the actual parameter.
              =do  ds<-hsVisiblePNs pn unfoldedDecl
                   (f,_)<-hsFreeAndDeclaredPNs exp
                   let clashedNames=filter (\x->elem (pNtoName x) (map pNtoName f)) (nub ds)
                   foldM (flip (autoRenameLocalVar False)) unfoldedDecl clashedNames

            doUnfolding' unfoldedDecl t pnt
              =applyTP (once_tdTP (failTP `adhocTP` exp)) t
                where
                  exp (e::HsExpP) --Because of the once_td traversal, the 'e' here must be the whole rhs or guard expression.
                    |findPNT pnt e
                    =if isComplexPatBind unfoldedDecl
                        then do replacePatCallByExp pnt unfoldedDecl e
                        else do let formalParams=paramsInDecl unfoldedDecl --get formalParams in unfolded declaration.
                                    actualParams=allParams pnt e     --get actual parameters.
                                    subst=zipWith (,) (map patToPN  formalParams) actualParams                         
                                unfoldedDecl'<-foldM  renameInUnfoldedDecl unfoldedDecl subst
                                --some formal parameters may have been renamed.
                                let formalParams'=paramsInDecl unfoldedDecl' 
                                    subst'=zipWith (,) (map patToPN formalParams') actualParams
                                    extraFormalParams=drop (length actualParams) formalParams'
                                decl'<-foldM replaceExp unfoldedDecl' subst'
                                let rhsExp=if extraFormalParams/=[]  --In case of partial application, convert extra
                                                                   --formal parameters into lambda exprssion.
                                        then (Exp (HsLambda extraFormalParams (fromJust (rhsExpInDecl decl'))))
                                        else fromJust (rhsExpInDecl decl')
                                    localDecls=hsDecls decl'
                                replaceFunCallByExp pnt rhsExp localDecls =<<(rmParams pnt (length subst') e) --do unfolding      
                  exp _=mzero
          
  
         --a pattern binding is a complex if the pattern is not a single variable.
        isComplexPatBind decl=case decl of
                   Dec (HsPatBind _ p _ _)->patToPN p ==defaultPN
                   _ ->False

        replacePatCallByExp pnt decl
         =applyTP (full_buTP (idTP `adhocTP` worker))
           where worker (e::HsExpP)
                  | sameOccurrence (expToPNT e) pnt   --in 'sameOccurrence', use location matters.
                     =do let newExp=Exp (HsParen (Exp (HsLet [decl] e)))
                         update e newExp e
                 worker x =return x

        ---replace the function name by it's defintion
        replaceFunCallByExp pnt exp localDecls
         = applyTP (full_buTP (idTP `adhocTP` worker)) 
           where worker (e::HsExpP)
                  |sameOccurrence (expToPNT e) pnt
                     =do let newExp=if localDecls/=[]
                                     then Exp (HsParen (Exp (HsLet localDecls exp)))
                                     else Exp (HsParen exp)  --Should check if exp is ready a Hsparen expression!
                         update e newExp e                        
                 worker x=return x

        --get the parameters in the declaration (there should be only once match).
        paramsInDecl decl = case decl of
                     (Dec (HsFunBind _ ((HsMatch _  _ pats _ _):_))) ->pats
                     _ ->[]
 
        --get the right hand side repression in a declaration
        rhsExpInDecl (Dec (HsFunBind _ ((HsMatch _ _  _ (HsBody e) _):_)))=Just e 
        rhsExpInDecl (Dec (HsPatBind _ _ (HsBody e) _))=Just e

         --get all the parameters to pnt (which is a function name) in expression 'exp'
        allParams pnt exp=allParams' pnt exp []
           where allParams' pnt exp initial -- pnt:function/pattern name.
                   =let p=getOneParam pnt exp
                    in if p/=defaultExp  then allParams' pnt (rmOneParam pnt exp) (initial++[p])         
                                         else initial

        --get the first parameter of pnt
        getOneParam pnt t
          =fromMaybe defaultExp (applyTU (once_tdTU (failTU `adhocTU` worker)) t)
             where
              worker (Exp (HsApp e1 e2))
                |sameOccurrence (expToPNT e1) pnt=Just e2
              worker _ =Nothing

        --remove the first parameter of pnt
        rmOneParam  pnt t
         =fromMaybe defaultExp (applyTP (stop_tdTP (failTP `adhocTP` worker)) t)
           where
             worker (Exp (HsApp e1 e2 ))
               |sameOccurrence (expToPNT e1) pnt =Just e1
             worker _=Nothing

        rmOneParamWithUpdToks pnt 
         =applyTP (stop_tdTP (failTP `adhocTP` inExp)) 
           where

             inExp (exp@(Exp (HsParen (Exp (HsApp e1 e2))))::HsExpP)
                |sameOccurrence (expToPNT e1) pnt 
                 =do update exp e1 exp    

             inExp exp@(Exp (HsApp e1 e2))
              | sameOccurrence (expToPNT e1) pnt
                 =do update exp e1 exp
             inExp  _=mzero
