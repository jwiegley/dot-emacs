

module RefacWhereLet(whereToLet) where

import PrettyPrint
import PosSyntax
import AbstractIO
import Data.Maybe
import TypedIds
import UniqueNames hiding (srcLoc)
import PNT
import TiPNT
import Data.List
import RefacUtils hiding (getParams)
import PFE0 (findFile)
import MUtils (( # ))
import RefacLocUtils
-- import System
import System.IO

{- This refactoring converts a where into a let. Could potentially narrow the scrope of those involved bindings.
   
   Copyright   :  (c) Christopher Brown 2008

   Maintainer  :  cmb21@kent.ac.uk
   Stability   :  provisional
   Portability :  portable   
   
-}

whereToLet args
 = do let fileName = ghead "filename" args 
          --fileName'= moduleName fileName
          --modName  = Module fileName'  
          row      = read (args!!1)::Int
          col      = read (args!!2)::Int
      modName <-fileNameToModName fileName

      (inscps, exps, mod, tokList)<-parseSourceFile fileName 
      let pnt = locToPNT fileName (row, col) mod 
      if not (checkInFun pnt mod)
        then error "Please select a definition within a where clause!"
        else do
              if (pnt /= defaultPNT)
               then do
                ((_,m), (newToks, newMod))<-applyRefac (doWhereToLet pnt) 
                                                       (Just (inscps, exps, mod, tokList)) fileName
                writeRefactoredFiles False [((fileName,m), (newToks,newMod))]
                AbstractIO.putStrLn "Completed.\n"
               else error "\nInvalid cursor position!"
  
doWhereToLet pnt (_,_,t)
 = do  
      mod <- convertToWhere pnt t
      return mod
      

convertToWhere pnt t
  = applyTP (full_tdTP (idTP `adhocTP` conInMatch
                             `adhocTP` conInPat
                             `adhocTP` conInAlt
                              )) t
      where
      
        conInMatch (match@(HsMatch loc name pats (HsBody e) ds)::HsMatchP)
         | canBeConverted ds pnt
             = do             
                  let decl = definingDecls [pNTtoPN pnt] ds True True
                  let updateRHS = (Exp (HsLet decl e))
                  ds' <- rmDecl (pNTtoPN pnt) True ds
                  -- we need to check that nothing else in the where
                  -- clause depends on this entity...
                  
                  allDecs <- mapM hsFreeAndDeclaredPNs ds'
                  if (declToPName2 $ ghead "conInMatch" decl) `elem` (concat (map fst allDecs))
                    then error "Entity cannot be converted as another declaration in the where clause depends on it!"
                    else do e' <- update e updateRHS e
                            return (HsMatch loc name pats (HsBody e') ds')
                  
        conInMatch (match@(HsMatch loc name pats g@(HsGuard e) ds)::HsMatchP)
         | canBeConverted ds pnt
             = do let decl = definingDecls [pNTtoPN pnt] ds True True
                  let updateRHS = (HsBody (Exp (HsLet decl (rmGuard g))))
                  ds' <- rmDecl (pNTtoPN pnt) True ds
                  allDecs <- mapM hsFreeAndDeclaredPNs ds'
                  if (declToPName2 $ ghead "conInMatch Guard" decl) `elem` (concat (map fst allDecs))
                    then error "Entity cannot be converted as another declaration in the where clause depends on it!"
                    else do e' <- update g updateRHS g
                            return (HsMatch loc name pats e' ds')

                 
        conInMatch x = return x 
        
        conInPat (pat@(Dec (HsPatBind loc p (HsBody e) ds))::HsDeclP)
         | canBeConverted ds pnt
             = do             
                  let decl = definingDecls [pNTtoPN pnt] ds True True
                  let updateRHS = (Exp (HsLet decl e))
                  ds' <- rmDecl (pNTtoPN pnt) True ds
                  allDecs <- mapM hsFreeAndDeclaredPNs ds'
                  if (declToPName2 $ ghead "conInPat" decl) `elem` (concat (map fst allDecs))
                    then error "Entity cannot be converted as another declaration in the where clause depends on it!"
                    else do e' <- update e updateRHS e
                            return (Dec (HsPatBind loc p (HsBody e') ds'))

                  
        conInPat (pat@(Dec (HsPatBind loc p g@(HsGuard e) ds))::HsDeclP)
         | canBeConverted ds pnt
             = do let decl = definingDecls [pNTtoPN pnt] ds True True
                  let updateRHS = (HsBody (Exp (HsLet decl (rmGuard g))))
                  ds' <- rmDecl (pNTtoPN pnt) True ds
                  allDecs <- mapM hsFreeAndDeclaredPNs ds'                  
                  if (declToPName2 $ ghead "conInPat" decl) `elem` (concat (map fst allDecs))
                    then error "Entity cannot be converted as another declaration in the where clause depends on it!"
                    else do e' <- update g updateRHS g
                            return (Dec (HsPatBind loc p e' ds'))


        conInPat x = return x
        
        
        conInAlt (alt@(HsAlt loc p (HsBody e) ds)::HsAltP)
         | canBeConverted ds pnt
            = do  let decl = definingDecls [pNTtoPN pnt] ds True True
                  let updateRHS = (Exp (HsLet decl e))
                  ds' <- rmDecl (pNTtoPN pnt) True ds
                  e' <- update e updateRHS e
                  return (HsAlt loc p (HsBody e') ds')
                  
        conInAlt (alt@(HsAlt loc p g@(HsGuard e) ds)::HsAltP)
         | canBeConverted ds pnt
             = do let decl = definingDecls [pNTtoPN pnt] ds True True
                  let updateRHS = (HsBody (Exp (HsLet decl (rmGuard g))))
                  ds' <- rmDecl (pNTtoPN pnt) True ds
                  e' <- updateGuardAlt g updateRHS g
                  return (HsAlt loc p e' ds')
       
        conInAlt x = return x
        
        updateGuardAlt oldRhs newRhs t
            = applyTP (once_tdTP (failTP `adhocTP` inRhs)) t
            where
              inRhs (r::RhsP)
               | r == oldRhs && srcLocs r == srcLocs oldRhs
                   = do (newRhs',_) <- updateToks oldRhs newRhs prettyprintGuardsAlt
                        return newRhs'
              inRhs r = mzero
        
        
        rmGuard ((HsGuard gs)::RhsP)
             = let (_,e1,e2)=glast "guardToIfThenElse" gs
               in  if ((pNtoName.expToPN) e1)=="otherwise" 
                   then (foldl mkIfThenElse e2 (tail(reverse gs)))
                   else (foldl mkIfThenElse defaultElse (reverse gs)) 
           
        mkIfThenElse e (_,e1, e2)=(Exp (HsIf e1 e2 e)) 

        defaultElse=(Exp (HsApp (Exp (HsId (HsVar (PNT (PN (UnQual "error") (G (PlainModule "Prelude") "error" 
                    (N (Just loc0)))) Value (N (Just loc0)))))) (Exp (HsLit loc0 (HsString "UnMatched Pattern")))))
                    
        
        canBeConverted :: [HsDeclP] -> PNT -> Bool
        canBeConverted ds pnt
          = pnt `elem` map declToPNT ds


checkInFun :: Term t =>  PNT -> t -> Bool
                     
checkInFun pnt t
  = checkInMatch pnt t || checkInPat pnt t || checkInAlt pnt t
  
  where
   checkInAlt pnt t
     = fromMaybe (False)
                 (applyTU (once_tdTU (failTU `adhocTU` inAlt)) t)
  
   checkInPat pnt t
     = fromMaybe (False)
                 (applyTU (once_tdTU (failTU `adhocTU` inPat)) t)
  
   checkInMatch pnt t
      = fromMaybe (False)
              (applyTU (once_tdTU (failTU `adhocTU` inMatch)) t)
    
   inAlt (alt@(HsAlt loc p rhs ds)::HsAltP)
      | findPNT pnt ds = Just True
   inAlt _ = Nothing

   --The selected sub-expression is in the rhs of a match
   inMatch (match@(HsMatch loc1  _ pats rhs ds)::HsMatchP)
    | findPNT pnt ds
          = Just True
   inMatch _ = Nothing

   --The selected sub-expression is in the rhs of a pattern-binding
   inPat (pat@(Dec (HsPatBind loc1 ps rhs ds))::HsDeclP)
     | findPNT pnt ds
          = Just True
   inPat _ = Nothing
