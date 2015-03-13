module RefacIntroPattern(introPattern, introCase, foldPattern) where

import TypeCheck
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
import PFE0 (findFile, allFiles, allModules)
import MUtils (( # ))
import RefacLocUtils
-- import System
import System.IO
import Relations
import Ents
import Data.Set (toList)
import Data.List


-- | An argument list for a function which of course is a list of paterns.
type FunctionPats = [HsPatP]

-- | A list of declarations used to represent a where or let clause.
type WhereDecls = [HsDeclP]


data PatFun = Mat | Patt | Er deriving (Eq, Show)

{- This module contains 3 refactorings for HaRe:
      introPattern : introduce a exhaustive pattern match for a 
                     selected pattern variable.
                     
      introCase    : introduce a case analysis over a selected
                     pattern variable. Introduces an exhaustive 
                     set of patterns for the type.
                     
      foldPattern  : allows one to fold a sub expression against a 
                     particular pattern variable
-}



{- Introduces pattern matching over a pattern variable. 
   Introduces an exhaustive set of patterns for a type 
   in a case analysis on the lhs of an equation.
   
   Copyright   :  (c) Christopher Brown 2008

   Maintainer  :  cmb21@kent.ac.uk
   Stability   :  provisional
   Portability :  portable   
   
-}

introPattern args
 = do let fileName = ghead "filename" args 
          --fileName'= moduleName fileName
          --modName  = Module fileName'  
          row      = read (args!!1)::Int
          col      = read (args!!2)::Int
      modName <-fileNameToModName fileName
      let modName1 = convertModName modName
      (inscps, exps, mod, tokList)<-parseSourceFile fileName
      -- (inscps3, exps3, mod3, tokList3)<-parsePrelude 
      let pnt = locToPNT fileName (row, col) mod
      if not (checkInPat pnt mod)
        then do 
                -- it's quite possible we are dealing with a sub-pattern
                -- let's check that case.
                if not (checkInSubPat pnt mod) 
                   then error "Please select a pattern variable on the LHS of an equation!"
                   else do
                           AbstractIO.putStrLn "introSubPattern"
                           ((_,m), (newToks, newMod))<-applyRefac (doIntroPatterns' fileName inscps pnt (modNameToStr modName)) 
                                                       (Just (inscps, exps, mod, tokList)) fileName
                           writeRefactoredFiles False [((fileName,m), (newToks,newMod))]
                           AbstractIO.putStrLn "Completed.\n"
        else do 
                AbstractIO.putStrLn "introPattern"
                ((_,m), (newToks, newMod))<-applyRefac (doIntroPatterns pnt) 
                                                       (Just (inscps, exps, mod, tokList)) fileName
                writeRefactoredFiles False [((fileName,m), (newToks,newMod))]
                AbstractIO.putStrLn "Completed.\n"

convertModName (PlainModule s) = s
convertModName m@(MainModule f) = modNameToStr m 


doIntroPatterns pnt (_,_,t)
 = do mod <- introPats pnt t
      return mod
      
doIntroPatterns' fileName inscps pnt modName (_,_,t)
 = do mod <- introPats' fileName inscps pnt modName t
      return mod
   
introPats pnt t
  = applyTP (full_tdTP (idTP `adhocTP` inDec)) t
     where
       inDec (dec@(Dec (HsFunBind s matches))::HsDeclP)
         | findPNT pnt matches && inMatch pnt matches
             = do
                  -- we need to find the type of the variable in question,
                  -- and also the implementation of the type. If the type
                  -- is defined outside of the project, we must error!
                  let match@(HsMatch loc name pats rhs ds) = getMatch pnt matches
                      typeSig = getTypeSig (pNTtoPN name) t
                      (typeOfPat, position) = findPatAndType 0 pnt (flatternType typeSig) pats
                      constrsOfData = findTypeAndConstrs 0 pnt (flatternType typeSig) pats     
                  -- check that argument position is a variable in all defining
                  -- equations...     
                  if checkVariableEquation matches position
                     then do
                           let newMatches = concatMap (createMatches dec (declToName dec) name pats  (position+1) constrsOfData) matches
                           update dec (Dec (HsFunBind s (newMatches++matches))) dec
                     else do
                           return dec 
       inDec x = return x                
       
       typToPNT (Typ (HsTyCon x)) = x      
       typToPNT x = error "Please select a variable with a type constructor!"
       
       checkVariableEquation [] _ = True
       checkVariableEquation ((HsMatch _ _ pats _ _):ms) position
        | checkPats (pats !! position) = checkVariableEquation ms position
        | otherwise = error "Pattern argument must be a variable in all defining equations!"
       
       checkPats (Pat (HsPIrrPat p)) = checkPats p
       checkPats (Pat (HsPParen p))  = checkPats p
       checkPats (Pat (HsPId (HsVar x))) = True
       checkPats _ = False
       
       createMatches (Dec (HsFunBind loc environment)) funName name pats position constrs match 
         = let (before, after)  = break (==match) environment
               newMatches = createMatches2 position (length pats) match constrs
           in newMatches
            where  
             createMatches2 _ _ _ [] = [] 
             createMatches2 position arity m@(HsMatch _ _ pats rhs ds)  ((ConInfo (PN n _) a _):cs)
              = let newPats = replace position pats (createPat pnt n a (pats !! (position-1)) (map pNtoName (hsPNs pats ++ hsPNs ds)))
                   in (HsMatch loc0 name newPats rhs ds) : createMatches2 position arity m cs
                 where
                   myReplicate 0 _ _  = []
                   myReplicate arity names index 
                      = let newName = mkNewName "a" names index
                        in (nameToPat newName) : (myReplicate (arity-1) (names ++ [newName]) (index+1))      

-- ==========================================================================
-- end of introPattern 
-- ==========================================================================

-- ==========================================================================
-- introduce sub pattern
-- ==========================================================================
introPats' fileName inscps pnt modName t
  = applyTP (full_tdTP (idTP `adhocTP` inDec)) t
     where
       inDec (dec@(Dec (HsFunBind s matches))::HsDeclP)
         | findPNT pnt matches && inMatch pnt matches
             = do
                  -- we need to find the type of the variable in question,
                  -- and also the implementation of the type. If the type
                  -- is defined outside of the project, we must error!
                  let match@(HsMatch loc name pats rhs ds) = getMatch pnt matches
                      typeSig = getTypeSig (pNTtoPN name) t
                      (typeOfPat, position) = findPatAndType 0 pnt (flatternType typeSig) pats
                      
                  -- we need to check to make sure there are no polymorphic. If they are we
                  -- can simply replace them with the () type. This seems to be the Haskell
                  -- equivalent of Null.
                  newTypeSig <- replacePolymorphicType typeSig
                      
                  let closureEquation = createClosure ((render.ppi) newTypeSig) (pNTtoName pnt) (pats !! position) position

                  -- res <- liftIO $ ghcTypeCheckPattern closureEquation "closure___" ses
                  typeOfPat2 <- getSigAsString fileName closureEquation (force $ ghcTypeCheckPattern closureEquation "closure___" modName fileName)
                  
                  -- this is necessary to force the evaluation of the GHC compiler,
                  -- since it's wrapped up in a naughty unsafePerformIO...
                  lift $ AbstractIO.putStrLn $ (typeOfPat2 \\ typeOfPat2)
                  
                  let typeOfPat2' = last $ typeAnnot' typeOfPat2
                  
                  let typeOfPat2Cleaned = cleanPatType typeOfPat2'
                      constrsOfData = extractConstructors typeOfPat2Cleaned (toList inscps)
                                    
                  let newMatches = createMatches dec (declToName dec) name pats position constrsOfData match
                      (beforeM, afterM) = break (==match) matches
                  update dec (Dec (HsFunBind s (beforeM ++ newMatches ++ afterM))) dec


       inDec x = return x                
       
       replacePolymorphicType typeSig
         = applyTP (full_tdTP (idTP `adhocTP` rename)) typeSig
            where
             rename (Typ (HsTyVar n)) = return (Typ (HsTyVar (nameToPNT "Int"))) 
             rename x = return x 
       
       
       force a = if a==a then a else a
       
       extractConstructors typeName [] = []
       extractConstructors typeName ((_,Ent _ (HsCon (SN n _)) (Type (TypeInfo _ cs _))):xs)
           | n == typeName && cs == [] = error $ "Cannot instantiate new patterns for the selected pattern. It may be of a polymorphic type, or a Haskell defined type such as Int."
           | n == typeName = cs
           | otherwise     = extractConstructors typeName xs
       extractConstructors typeName (x:xs) = extractConstructors typeName xs
       
       cleanPatType [] = []
       cleanPatType (' ':xs) = cleanPatType xs
       cleanPatType ('[':xs) = "[]"
       cleanPatType ('(':xs) 
         = "(" ++ ( filter (==',') xs) ++ ")"
       cleanPatType xs = let (x, s') = break (== ' ') xs
                          in x
       
       getSigAsString ses closureEquation res
         = do
            let types = lines2 res            
            let types1 = cleanTypes (tail types)
            let (context, l) = getContext (head types)
            let types2 = l : types1
            let types3 = map (filter (/= '\n')) types2
            let types4 = fold (tail types3)
      
            return (context ++ " => " ++ (head types3) ++ " -> " ++ types4) 
             where 
              fold [] = []
              fold [x] = x
              fold  (x:xs) = x ++ (" -> " ++ fold xs) 
       
       createClosure :: String -> String -> HsPatP -> Int -> String
       createClosure typeSig p pat pos
         =   "(\\(" ++ ((render.ppi) pat) ++ "::" ++ ((typeAnnot typeSig)!!pos) ++ ") -> " ++ p ++")"
        -- =  "closure___ " ++ "(" ++ ((render.ppi) pat) ++ "::" ++ ((typeAnnot typeSig)!!pos) ++ ") = " ++ p
              where
       typeAnnot :: String -> [String]
       typeAnnot "" = []
       typeAnnot s = let (_, s') = break (== ':') s
                       in case s' of
                             { [] -> [];
                               (_:s'') -> typeAnnot' (tail s'') }
       typeAnnot' :: String -> [String]
       typeAnnot' "" =  []
       typeAnnot' s =  let (l, s') = break (== '-') s
                         in  l : case s' of
                                    {[] -> [];
                                     (_:s'') -> typeAnnot' (tail s'')}
         
       

       
       
       getModuleName [] modName = ""
       getModuleName (t:ts) modName
         | stripFilePath t == modName = t
         | otherwise                  = getModuleName ts modName
           where
             stripFilePath t 
               = let (f,_) = break (=='/') (reverse t);
                     (f',_) = break ( =='.') (reverse f) in f'
       
       createMatches (Dec (HsFunBind loc environment)) funName name pats position constrs match 
         = let (before, after)  = break (==match) environment
               newMatches = createMatches2 position (length pats) match constrs
           in newMatches
            where  
             createMatches2 _ _ _ [] = [] 
             createMatches2 position arity m@(HsMatch _ _ pats rhs ds)  ((ConInfo (SN n _) a _):cs)
              = -- only update the pattern we are interested in...
                let newPats = replace (position+1) pats (createSubPat pnt n a (pats !! position) (map pNtoName (hsPNs pats ++ hsPNs ds)))
                     in (HsMatch loc0 name newPats rhs ds) : createMatches2 position arity m cs
              
              
               -- let newPats = replace position pats (createPat pnt n a (pats !! position) (map pNtoName (hsPNs pats ++ hsPNs ds)))
               --    in (HsMatch loc0 name newPats rhs ds) : createMatches2 position arity m cs
                 where
                   myReplicate 0 _ _  = []
                   myReplicate arity names index 
                      = let newName = mkNewName "a" names index
                        in (nameToPat newName) : (myReplicate (arity-1) (names ++ [newName]) (index+1))
       
       createSubPat :: PNT -> String -> Int -> HsPatP -> [String] -> HsPatP
       createSubPat pnt x i (Pat (HsPParen p)) environ = (Pat (HsPParen (createSubPat pnt x i p environ)))
       createSubPat pnt x i (Pat (HsPApp n p)) environ
            = let myTail [] = []
                  myTail [x] = []
                  myTail (x:xs) = xs
                  (before, a) = break (findPNT pnt) p
              in case a of
                  [] -> createSubPat'' pnt x i environ 
                  after -> (Pat (HsPApp n (before ++ [createSubPat pnt x i (ghead "createSubPat" after) environ] ++ (myTail after))))
       createSubPat pnt x i (Pat (HsPTuple s p)) environ
         = let myTail [] = []
               myTail [x] = []
               myTail (x:xs) = xs
               (before, a) = break (findPNT pnt) p
           in case a of
                [] -> createSubPat'' pnt x i environ -- create the sub pattern and get out of here!
                after -> (Pat (HsPTuple s (before ++ [createSubPat pnt x i (ghead "createSubPat" after) environ] ++ (myTail after))))
             
       createSubPat pnt x i (Pat (HsPIrrPat p)) environ
           = (Pat (HsPIrrPat (createSubPat pnt x i p environ)))
        
       createSubPat pnt x i (Pat (HsPInfixApp p1 i2 p2)) environ
         | findPNT pnt p1 = (Pat (HsPInfixApp (createSubPat pnt x i p1 environ) i2 p2))
         | findPNT pnt p2 = (Pat (HsPInfixApp p1 i2 (createSubPat pnt x i p2 environ)))
       
       createSubPat pnt x i (Pat (HsPAsPat n p)) environ
         = (Pat (HsPAsPat n (createSubPat pnt x i p environ)))  
           
       createSubPat pnt x i _ environ = createSubPat' pnt x i environ

       createSubPat' pnt i 0 environ = Pat (HsPAsPat pnt (Pat (HsPId (HsCon (nameToPNT i)))))
       createSubPat' pnt x@(':':xs) ts environ
          = Pat (HsPAsPat pnt (Pat (HsPInfixApp (ghead "createPat" pat1) (nameToPNT x) 
                                                                 (last pat1))))
          where 
           pat1 = reverse $ createId environ ts 
       createSubPat' pnt x@('(':xs) ts environ
         = Pat (HsPAsPat pnt (Pat ( HsPTuple loc0 (reverse (createId environ ts)))))                    
       createSubPat' pnt i ts environ = Pat (HsPAsPat pnt (Pat (HsPApp (nameToPNT i) (reverse (createId environ ts)))))
       
       createSubPat'' pnt i 0 environ = (Pat (HsPId (HsCon (nameToPNT i))))
       createSubPat'' pnt x@(':':xs) ts environ
          = (Pat (HsPInfixApp (ghead "createPat" pat1) (nameToPNT x) 
                                                                 (last pat1)))
          where 
           pat1 = reverse $ createId environ ts 
       createSubPat'' pnt x@('(':xs) ts environ
         = (Pat ( HsPTuple loc0 (reverse (createId environ ts))))                      
       createSubPat'' pnt i ts environ = (Pat (HsPApp (nameToPNT i) (reverse (createId environ ts))))
       
       
       findType index _ _ [] = error "No type associated with pattern variable!"
       findType index pnt types (p:ps) 
         | findPNT pnt p = extractTypeName (types !! index)
         | otherwise     = findType (index+1) pnt types ps 

       extractTypeName (Typ (HsTyCon (PNT pn (Type (TypeInfo _ cs _)) _ ))) = pn
       extractTypeName (Typ (HsTyVar (PNT pn _ _))) = pn
       extractTypeName x = error "Please select a variable with a type constructor!"  
       
       extractTypeImplem [] typeName = error (typeName ++ " cannot be found in this project!")
       extractTypeImplem (d:ds) typeName
         | declToName d == typeName = d
         | otherwise                = extractTypeImplem ds typeName
       
       
       constrsToModule (PNT (PN _ (G (PlainModule m) _ _)) _ _) = m
       constrsToModule (PNT p@(PN _ (G (MainModule m) _ _)) _ _) = "Main"
       constrsToModule x = error "Error in constrsToModule!"
              
       
       findPatAndType index _ _ [] = error "No type associated with pattern variable!"
       findPatAndType index pnt types (p:ps)
          | findPNT' pnt [p] = (typToPNT (types !! index), index)
          | otherwise     = findPatAndType (index+1) pnt types ps
       
       findConstrAndType pnt pat typeOfPat
          = (positionOfPat, typ) 
             where
               positionOfPat = flatternPat pnt pat
               typ     = extractType positionOfPat constr typeOfPat
               constr = findConstr pnt pat
       
       extractType pos constr d@(Dec (HsDataDecl _ _ _ cs _))
          = extractCons cs
             where
                extractCons [] = error "This is not a valid parameter of the binding constructor!"
                extractCons ((HsConDecl _ _ _ n types) : more)
                  | ghead "extractCons" (pNTtoName constr) == '(' &&
                    pNTtoName n == pNTtoName constr = removeBang (types !! pos)
                  | n == constr = removeBang (types !! pos)
                  | otherwise = extractCons more
                    where
                      removeBang (HsBangedType t) = t
                      removeBang (HsUnBangedType t) = t
       
       findPosition index pnt [] = 0
       findPosition index pnt (p:ps)
        | findPNT pnt p = index
        | otherwise     = findPosition (index+1) pnt ps
        
          
       flatternPat pnt (Pat (HsPAsPat i p)) = flatternPat pnt p
       flatternPat pnt (Pat (HsPApp i p)) 
        | findPNT pnt p = findPosition 0 pnt p
       flatternPat pnt (Pat (HsPTuple _ p))
        | findPNT pnt p = findPosition 0 pnt p
       flatternPat pnt (Pat (HsPInfixApp p1 i p2)) = findPosition 0 pnt [p1] + findPosition 1 pnt [p2]
       flatternPat pnt (Pat (HsPParen p)) = flatternPat pnt p
       -- flatternPat pnt (Pat (HsPId i)) = 1
       flatternPat pnt p = error "Selected pattern is not a sub-pattern in flatternPat"   
          
       findConstr pnt (Pat (HsPAsPat i p))
         = findConstr pnt p
       findConstr pnt (Pat (HsPApp i p))
         | findPNT' pnt p = i
       findConstr pnt (Pat (HsPTuple _ p))
         | findPNT' pnt p = nameToPNT "(,)"  -- this needs checking for arbitrary sized tuples
       findConstr pnt (Pat (HsPInfixApp p1 i p2))
         | findPNT pnt p1 || findPNT pnt p2 = i
       findConstr pnt (p@(Pat (HsPParen p1)))
          = findConstr pnt p1
       findConstr pnt (p@(Pat (HsPId (HsCon i)))) 
         | findPNT pnt p = i
       findConstr pnt p = error "pattern is not bound to a constructor entity!" 
       
       findPNT' pnt []     = False
       findPNT' pnt ((Pat (HsPAsPat i p)):ps)
         | findPNT pnt i    = True
         | findPNT' pnt [p] = True
         | otherwise        = findPNT' pnt ps
       findPNT' pnt ((Pat (HsPApp i ps)):pss)
         | findPNT' pnt ps = True
         | otherwise     = findPNT' pnt ps
       findPNT' pnt ((Pat (HsPTuple i ps)):pss)
         | findPNT' pnt ps = True
         | otherwise     = findPNT' pnt ps        
       findPNT' pnt (Pat (HsPInfixApp p1 i p2):ps)
         | findPNT pnt p1 || findPNT pnt p2 = True
         | otherwise  = findPNT' pnt ps
       findPNT' pnt (p@(Pat (HsPParen p1)):ps)
         | findPNT' pnt [p1] = True
         | otherwise     = findPNT' pnt ps
       findPNT' pnt (p@(Pat (HsPId x)):ps) 
         | findPNT pnt p = True
         | otherwise     = findPNT' pnt ps
       findPNT' pnt (p:ps) = findPNT' pnt ps
       
       
       typToPNT (Typ (HsTyCon x)) = x      
       typToPNT x = error "Please select a variable with a type constructor!"
       
       checkVariableEquation [] _ = True
       checkVariableEquation ((HsMatch _ _ pats _ _):ms) position
        | checkPats (pats !! position) = checkVariableEquation ms position
        | otherwise = error "Pattern argument must be a variable in all defining equations!"
       
       checkPats (Pat (HsPIrrPat p)) = checkPats p
       checkPats (Pat (HsPParen p))  = checkPats p
       checkPats (Pat (HsPId (HsVar x))) = True
       checkPats _ = False

-- ==========================================================================
-- end of introSubPattern 
-- ==========================================================================

introCase args
 = do let fileName = ghead "filename" args 
          --fileName'= moduleName fileName
          --modName  = Module fileName'  
          row      = read (args!!1)::Int
          col      = read (args!!2)::Int
      modName <-fileNameToModName fileName
      let modName1 = convertModName modName
      (inscps, exps, mod, tokList)<-parseSourceFile fileName
      let pnt = locToPNT fileName (row, col) mod
      if not (checkInPat pnt mod)
        then do
                if not (checkInSubPat pnt mod) 
                   then error "Please select a pattern variable on the LHS of an equation!"
                   else do
                           AbstractIO.putStrLn "introCaseSubPattern"
                           ((_,m), (newToks, newMod))<-applyRefac (doIntroCasePatterns' fileName inscps pnt (modNameToStr modName)) 
                                                       (Just (inscps, exps, mod, tokList)) fileName
                           writeRefactoredFiles False [((fileName,m), (newToks,newMod))]
                           AbstractIO.putStrLn "Completed.\n"
        else do 
                AbstractIO.putStrLn "introCasePattern"
                ((_,m), (newToks, newMod))<-applyRefac (doIntroCasePatterns pnt) 
                                                       (Just (inscps, exps, mod, tokList)) fileName
                writeRefactoredFiles False [((fileName,m), (newToks,newMod))]
                AbstractIO.putStrLn "Completed.\n"

 
doIntroCasePatterns pnt (_,_,t)
 = do mod <- introPatsCase pnt t
      return mod
      
doIntroCasePatterns' fileName inscps pnt modName (_,_,t)
 = do mod <- introPatsCase' fileName inscps pnt modName t
      return mod

introPatsCase' fileName inscps pnt modName t
  = applyTP (full_tdTP (idTP `adhocTP` inDec)) t
     where
       inDec (dec@(Dec (HsFunBind s matches))::HsDeclP)
         | findPNT pnt matches && inMatch pnt matches
             = do
                  -- we need to find the type of the variable in question,
                  -- and also the implementation of the type. If the type
                  -- is defined outside of the project, we must error!
                  let match@(HsMatch loc name pats rhs ds) = getMatch pnt matches
                      typeSig = getTypeSig (pNTtoPN name) t
                      (typeOfPat, position) = findPatAndType 0 pnt (flatternType typeSig) pats
                      
                  -- we need to check to make sure there are no polymorphic. If they are we
                  -- can simply replace them with the () type. This seems to be the Haskell
                  -- equivalent of Null.
                  newTypeSig <- replacePolymorphicType typeSig    
                      
                  let closureEquation = createClosure ((render.ppi) newTypeSig) (pNTtoName pnt) (pats !! position) position

                  -- error $ "RefacIntroPattern.introPatsCase': ghcTypeCheckPattern params" ++ (show (closureEquation,"closure___",modName,fileName))-- ++AZ++    
                  -- res <- liftIO $ ghcTypeCheckPattern closureEquation "closure___" ses
                  typeOfPat2 <- getSigAsString fileName closureEquation (force $ ghcTypeCheckPattern closureEquation "closure___" modName fileName)
                  
                  -- this is necessary to force the evaluation of the GHC compiler,
                  -- since it's wrapped up in a naughty unsafePerformIO...
                  lift $ AbstractIO.putStrLn $ (typeOfPat2 \\ typeOfPat2)
                  
                  let typeOfPat2' = last $ typeAnnot' typeOfPat2
                  
                  let typeOfPat2Cleaned = cleanPatType typeOfPat2'
                      constrsOfData = extractConstructors typeOfPat2Cleaned (toList inscps)
                  
                  let newMatches = createMatches dec (declToName dec) pnt name pats position constrsOfData match
                      (beforeM, afterM) = break (==match) matches
                  update dec (Dec (HsFunBind s (beforeM ++ newMatches ++ afterM))) dec
       inDec x = return x           
        
        
       createMatches (Dec (HsFunBind loc environment)) funName pnt name pats position constrs match 
         = let (before, after)  = break (==match) environment
               newMatches = createMatches2 position (length pats) match constrs
           in newMatches
            where  
             createMatches2 _ _ _ [] = []
             createMatches2 position arity m@(HsMatch _ _ pats rhs ds) constrs@(c:cs)
              = [HsMatch loc0 name pats newCase ds]
                 where
                   newPats [] = []
                   newPats ((ConInfo (SN n _) a _):cs) = createPat pnt n a (pats !! position)
                                                                           (map pNtoName (hsPNs pats ++ hsPNs ds))
                                                            : newPats cs
                   newCase = HsBody (Exp (HsCase (nameToExp (pNTtoName pnt)) (newAlts (newPats constrs))))
                   newAlts [] = []
                   newAlts (p:ps) = (HsAlt loc0 p rhs []) : newAlts ps
                 
                   myReplicate 0 _ _  = []
                   myReplicate arity names index 
                      = let newName = mkNewName "a" names index
                        in (nameToPat newName) : (myReplicate (arity-1) (names ++ [newName]) (index+1)) 
           
       replacePolymorphicType typeSig
         = applyTP (full_tdTP (idTP `adhocTP` rename)) typeSig
            where
             rename (Typ (HsTyVar n)) = return (Typ (HsTyVar (nameToPNT "Int"))) 
             rename x = return x 
       
       
       force a = if a==a then a else a
       
       extractConstructors typeName [] = []
       extractConstructors typeName ((_,Ent _ (HsCon (SN n _)) (Type (TypeInfo _ cs _))):xs)
           | n == typeName && cs == [] = error $ "Cannot instantiate new patterns for the selected pattern. It may be of a polymorphic type, or a Haskell defined type such as Int."
           | n == typeName = cs
           | otherwise     = extractConstructors typeName xs
       extractConstructors typeName (x:xs) = extractConstructors typeName xs
       
       cleanPatType [] = []
       cleanPatType (' ':xs) = cleanPatType xs
       cleanPatType ('[':xs) = "[]"
       cleanPatType ('(':xs) 
         = "(" ++ ( filter (==',') xs) ++ ")"
       cleanPatType xs = let (x, s') = break (== ' ') xs
                          in x
       
       getSigAsString ses closureEquation res
         = do
            let types = lines2 res            
            let types1 = cleanTypes (tail types)
            let (context, l) = getContext (head types)
            let types2 = l : types1
            let types3 = map (filter (/= '\n')) types2
            let types4 = fold (tail types3)
      
            return (context ++ " => " ++ (head types3) ++ " -> " ++ types4) 
             where 
              fold [] = []
              fold [x] = x
              fold  (x:xs) = x ++ (" -> " ++ fold xs)    
       
       createClosure :: String -> String -> HsPatP -> Int -> String
       createClosure typeSig p pat pos
         =   "(\\(" ++ ((render.ppi) pat) ++ "::" ++ ((typeAnnot typeSig)!!pos) ++ ") -> " ++ p ++")"
        -- =  "closure___ " ++ "(" ++ ((render.ppi) pat) ++ "::" ++ ((typeAnnot typeSig)!!pos) ++ ") = " ++ p
              where        
       typeAnnot :: String -> [String]
       typeAnnot "" = []
       typeAnnot s = let (_, s') = break (== ':') s
                       in case s' of
                             { [] -> [];
                               (_:s'') -> typeAnnot' (tail s'') }
       typeAnnot' :: String -> [String]
       typeAnnot' "" =  []
       typeAnnot' s =  let (l, s') = break (== '-') s
                         in  l : case s' of
                                    {[] -> [];
                                     (_:s'') -> typeAnnot' (tail s'')} 
                  
introPatsCase pnt t
  = applyTP (full_tdTP (idTP `adhocTP` inDec)) t
     where
       inDec (dec@(Dec (HsFunBind s matches))::HsDeclP)
         | findPNT pnt matches && inMatch pnt matches
             = do
                  -- we need to find the type of the variable in question,
                  -- and also the implementation of the type. If the type
                  -- is defined outside of the project, we must error!
                  let match@(HsMatch loc name pats rhs ds) = getMatch pnt matches
                      typeSig = getTypeSig (pNTtoPN name) t
                      (typeOfPat, position) = findPatAndType 0 pnt (flatternType typeSig) pats
                      constrsOfData = findTypeAndConstrs 0 pnt (flatternType typeSig) pats     
                  -- check that argument position is a variable in all defining
                  -- equations...     
                  if checkVariableEquation matches position
                     then do
                           let newMatches = concatMap (createMatches dec (declToName dec) name pats  (position+1) constrsOfData) matches
                           update dec (Dec (HsFunBind s (newMatches++matches))) dec
                     else do
                           return dec 
       inDec x = return x        
      
       typToPNT (Typ (HsTyCon x)) = x      
       typToPNT x = error "Please select a variable with a type constructor1!"
      
       checkVariableEquation [] _ = True
       checkVariableEquation ((HsMatch _ _ pats _ _):ms) position
        | checkPats (pats !! position) = checkVariableEquation ms position
        | otherwise = error "Pattern argument must be a variable in all defining equations!"
       
       checkPats (Pat (HsPIrrPat p)) = checkPats p
       checkPats (Pat (HsPParen p))  = checkPats p
       checkPats (Pat (HsPId (HsVar x))) = True
       checkPats _ = False
       
       createMatches (Dec (HsFunBind loc environment)) funName name pats position constrs match 
         = let (before, after)  = break (==match) environment
               newMatches = createMatches2 position (length pats) match constrs
           in newMatches
            where  
             createMatches2 _ _ _ [] = []
             createMatches2 position arity m@(HsMatch _ _ pats rhs ds) constrs@(c:cs)
              = [HsMatch loc0 name pats newCase ds]
                 where
                   newPats [] = []
                   newPats ((ConInfo (PN n _) a _):cs) = createPat pnt n a (pats !! (position-1)) 
                                                                           (map pNtoName (hsPNs pats ++ hsPNs ds))
                                                            : newPats cs
                   newCase = HsBody (Exp (HsCase (nameToExp (pNtoName (patToPN (pats !! (position-1))))) (newAlts (newPats constrs) )))
                   newAlts [] = []
                   newAlts (p:ps) = (HsAlt loc0 p rhs []) : newAlts ps
                 
                   myReplicate 0 _ _  = []
                   myReplicate arity names index 
                      = let newName = mkNewName "a" names index
                        in (nameToPat newName) : (myReplicate (arity-1) (names ++ [newName]) (index+1))
-- ==========================================================================
-- end of introCase
-- ==========================================================================            
            
foldPattern args
 = do let fileName = ghead "filename" args 
          --fileName'= moduleName fileName
          --modName  = Module fileName' 
          patName  = (args!!1)
          beginRow = read (args!!2)::Int
          beginCol = read (args!!3)::Int 
          endRow   = read (args!!4)::Int
          endCol   = read (args!!5)::Int
      modName <-fileNameToModName fileName
      (inscps, exps, mod, tokList)<-parseSourceFile fileName 
      
      let (ty, pnt, pats, subExp, wh)
             = findDefNameAndExp tokList
                                 (beginRow, beginCol)
                                 (endRow, endCol)
                                 mod
      let exp = locToExp (beginRow, beginCol)
                         (endRow, endCol)
                         tokList
                         mod
                         
      ((_,m), (newToks, newMod))<-applyRefac (doFoldPattern patName pnt exp) 
                                             (Just (inscps, exps, mod, tokList)) fileName
      writeRefactoredFiles False [((fileName,m), (newToks,newMod))]
      AbstractIO.putStrLn "Completed.\n"                   

doFoldPattern patName pnt exp (_,_,t)
 = do
      mod <- foldPatterns patName pnt exp t
      return mod

foldPatterns patName pnt exp t
   = applyTP (stop_tdTP (failTP `adhocTP` inMod
                              `adhocTP` inMatch)) t
       where
        inMod (mod@(HsModule loc name exps imps ds):: HsModuleP)
         | pnt `elem` (map declToPNT ds) 
             = do
                  ds' <- doFoldModule ds
                  return (HsModule loc name exps imps ds')
            where
             doFoldModule t
              = applyTP (stop_tdTP (failTP `adhocTP` inMatch2)) t
               where
               inMatch2 (match@(HsMatch loc name pats rhs ds)::HsMatchP)
                | useLoc pnt == useLoc name
                    = do
                         -- let's check that the pattern name
                         -- occurs as a variable pattern in pats
                         if checkPattern patName pats == False
                           then error "The pattern entered does not occur with the pattern list or is not a pattern variable!"
                           else do 
                                  -- let's replace the highlighted expression with the pattern name
                                  newExp <- replaceExp rhs patName exp
                                  return (HsMatch loc name pats newExp ds)
               inMatch2 x = mzero  

        inMod x = mzero    
        
        inMatch (match@(HsMatch loc name pats rhs ds)::HsMatchP)
         | useLoc pnt == useLoc name
            =do
               -- let's check that the pattern name
               -- occurs as a variable pattern in pats
               if checkPattern patName pats == False
                 then error "The pattern entered does not occur with the pattern list or is not a pattern variable!"
                 else do 
                        -- let's replace the highlighted expression with the pattern name
                        newExp <- replaceExp rhs patName exp
                        return (HsMatch loc name pats newExp ds)
      
        inMatch x = mzero

replaceExp t patName e
    = applyTP (stop_tdTP (failTP `adhocTP` subExp)) t
       where 
         subExp exp@((Exp _)::HsExpP)
          | sameOccurrence exp e == True
               = update exp (nameToExp patName) exp
          | otherwise = mzero


checkPattern :: String -> [HsPatP] -> Bool
checkPattern patName
 = (fromMaybe False).applyTU (once_tdTU (failTU `adhocTU` inVar))
     where
       inVar (Pat (HsPId (HsVar n)))
         | pNTtoName n  == patName = Just True
       inVar (Pat (HsPAsPat n p))
         | pNTtoName n == patName = Just True
       inVar x = Nothing

                
-- ==========================================================================
-- end of foldPattern
-- ==========================================================================
             
-- utility functions    

{-|
Takes the position of the highlighted code and returns
the function name, the list of arguments, the expression that has been
highlighted by the user, and any where\/let clauses associated with the
function. 
-}

findDefNameAndExp :: Term t => [PosToken] -- ^ The token stream for the 
                                          -- file to be
                                          -- refactored.
                  -> (Int, Int) -- ^ The beginning position of the highlighting.
                  -> (Int, Int) -- ^ The end position of the highlighting.
                  -> t          -- ^ The abstract syntax tree.
                  -> (PatFun, PNT, FunctionPats, HsExpP, WhereDecls) -- ^ A tuple of,
                     -- (the function name, the list of arguments,
                     -- the expression highlighted, any where\/let clauses
                     -- associated with the function).
                     
findDefNameAndExp toks beginPos endPos t
  = fromMaybe (Er, defaultPNT, [], defaultExp, [])
              (applyTU (once_buTU (failTU `adhocTU` inMatch `adhocTU` inPat)) t)

    where
      --The selected sub-expression is in the rhs of a match
      inMatch (match@(HsMatch loc1  pnt pats rhs@(HsBody e) ds)::HsMatchP)
        | locToExp beginPos endPos toks rhs /= defaultExp
          = Just (Mat, pnt, pats, locToExp beginPos endPos toks rhs, ds)
      inMatch (match@(HsMatch loc1  pnt pats rhs@(HsGuard e) ds)::HsMatchP)
        | locToExp beginPos endPos toks rhs /= defaultExp
          = Just (Mat, pnt, pats, rmGuard rhs, ds)          
      inMatch _ = Nothing

      --The selected sub-expression is in the rhs of a pattern-binding
      inPat (pat@(Dec (HsPatBind loc1 ps rhs ds))::HsDeclP)
        | locToExp beginPos endPos toks rhs /= defaultExp
          = error "Cannot fold against a variable within a pattern binding!"
      inPat _ = Nothing

      rmGuard ((HsGuard gs)::RhsP)
             = let (_,e1,e2)=glast "guardToIfThenElse" gs
               in  if ((pNtoName.expToPN) e1)=="otherwise" 
                   then (foldl mkIfThenElse e2 (tail(reverse gs)))
                   else (foldl mkIfThenElse defaultElse (reverse gs)) 
           
      mkIfThenElse e (_,e1, e2)=(Exp (HsIf e1 e2 e)) 

      defaultElse=(Exp (HsApp (Exp (HsId (HsVar (PNT (PN (UnQual "error") (G (PlainModule "Prelude") "error" 
                    (N (Just loc0)))) Value (N (Just loc0)))))) (Exp (HsLit loc0 (HsString "UnMatched Pattern")))))


         
checkInPat :: Term t =>  PNT -> t -> Bool
checkInPat pnt t
  = checkInMatch pnt t
  where
   checkInMatch pnt t
     = fromMaybe (False)
                 (applyTU (once_tdTU (failTU `adhocTU` inMatch)) t)
   --The selected sub-expression is in the rhs of a match
   inMatch (match@(HsMatch loc1  _ pats rhs ds)::HsMatchP)
    | findPNT' pnt pats
          = Just True
       where findPNT' pnt []     = False
             findPNT' pnt (p@(Pat (HsPIrrPat p1)):ps)
              | findPNT pnt p1 = True
              | otherwise     = findPNT' pnt ps
             findPNT' pnt (p@(Pat (HsPParen p1)):ps)
              | findPNT' pnt [p1] = True
              | otherwise     = findPNT' pnt ps
             findPNT' pnt (p@(Pat (HsPId x)):ps) 
              | findPNT pnt p = True
              | otherwise     = findPNT' pnt ps
             findPNT' pnt (p:ps) = findPNT' pnt ps
   inMatch _ = Nothing

checkInSubPat :: Term t =>  PNT -> t -> Bool
checkInSubPat pnt t
  = checkInPat pnt t
  where
   checkInPat pnt t
     = fromMaybe (False)
                 (applyTU (once_tdTU (failTU `adhocTU` inMatch)) t)
   --The selected sub-expression is in the rhs of a match
   inMatch (match@(HsMatch loc1  _ pats rhs ds)::HsMatchP)
    | findPNT' pnt pats
          = Just True
       where findPNT' pnt []     = False
             findPNT' pnt ((Pat (HsPAsPat i p)):ps)
              | findPNT pnt i    = True
              | findPNT' pnt [p] = True
              | otherwise        = findPNT' pnt ps
             findPNT' pnt ((Pat (HsPApp i ps)):pss)
              | findPNT' pnt ps = True
              | otherwise     = findPNT' pnt ps
             findPNT' pnt ((Pat (HsPTuple _ ps)):pss)
              | findPNT' pnt ps = True
              | otherwise       = findPNT' pnt ps
             findPNT' pnt (Pat (HsPInfixApp p1 i p2):ps)
              | findPNT pnt p1 || findPNT pnt p2 = True
              | otherwise  = findPNT' pnt ps
             findPNT' pnt (p@(Pat (HsPParen p1)):ps)
              | findPNT' pnt [p1] = True
              | otherwise     = findPNT' pnt ps
             findPNT' pnt (p@(Pat (HsPId x)):ps) 
              | findPNT pnt p = True
              | otherwise     = findPNT' pnt ps
             findPNT' pnt (p:ps) = findPNT' pnt ps
   inMatch _ = Nothing

createPat :: PNT -> String -> Int -> HsPatP -> [String] -> HsPatP
createPat pnt x i (Pat (HsPIrrPat p)) environ
    = (Pat (HsPIrrPat (createPat' pnt x i environ)))
createPat pnt x i _ environ = createPat' pnt x i environ

createPat' pnt i 0 environ = Pat (HsPAsPat pnt (Pat (HsPId (HsCon (nameToPNT i)))))
createPat' pnt x@(':':xs) ts environ
  = Pat (HsPAsPat pnt (Pat (HsPInfixApp (ghead "createPat" pat1) (nameToPNT x) 
                                                                 (last pat1))))
       where 
         pat1 = reverse $ createId environ ts
createPat' pnt x@('(':xs) ts environ
   = Pat (HsPAsPat pnt (Pat ( HsPTuple loc0 (reverse (createId environ ts)))))                      
createPat' pnt i ts environ = Pat (HsPAsPat pnt (Pat (HsPApp (nameToPNT i) (reverse (createId environ ts)))))

createId _ 0 = []
createId names a
   = let newName = mkNewName "b" names a
     in (nameToPat newName) : (createId (names ++ [newName]) (a-1))
                 
                 
replace :: Int -> [a] -> a -> [a]
replace pos [] e = []
replace pos list e
   = (init (take pos list)) ++ [e] ++ (drop pos list) 

inMatch _ [] = False
inMatch pnt (match@(HsMatch loc name pats rhs ds):ms)
  | findPNT pnt pats = True
  | otherwise        = inMatch pnt ms
 
getMatch _ [] = error "Please select a pattern variable on the LHS of an equation!"
getMatch pnt (match@(HsMatch loc name pats rhs ds):ms)
  | findPNT pnt pats = match
  | otherwise        = getMatch pnt ms
                       

 
getTypeSig name t
  = fromMaybe (error "Please define a type signature for the definition!")
              (applyTU (once_tdTU (failTU `adhocTU` inDec)) t)
   where
     inDec (d@(Dec (HsTypeSig _ _ _ _))::HsDeclP)
        | definesTypeSig name d = Just d
     inDec _ = Nothing
 
findTypeAndConstrs index _ _ [] = error "No type associated with pattern variable!"
findTypeAndConstrs index pnt types (p:ps) 
  | findPNT pnt p = extractConstrs (types !! index)
  | otherwise     = findTypeAndConstrs (index+1) pnt types ps              
         
findPatAndType index _ _ [] = error "No type associated with pattern variable!"
findPatAndType index pnt types (p:ps) 
  | findPNT pnt p = (typToPNT (types !! index), index)
  | otherwise     = findPatAndType (index+1) pnt types ps
        
-- flatternType :: HsDeclP -> [HsTypeP]
flatternType (Dec (HsTypeSig _ _ _ t))
  = flatternT t
flatternT (Typ (HsTyApp t1 t2)) = flatternT t1 
flatternT (Typ (HsTyFun t1 t2)) = flatternT t1 ++ flatternT t2 
flatternT (Typ (HsTyForall _ _ t)) = flatternT t
flatternT t = [t]

flatternAllType (Dec (HsTypeSig _ _ _ t))
  = flatternAllT t
flatternAllT (Typ (HsTyApp t1 t2))
  = flatternAllT t1 ++ flatternAllT t2
 --  | pNTtoName (typToPNT t1) == "[]" = flatternAllT t1
 -- | otherwise = flatternAllT t1 ++ flatternAllT t2
flatternAllT (Typ (HsTyFun t1 t2)) = flatternAllT t1 ++ flatternAllT t2 
flatternAllT (Typ (HsTyForall _ _ t)) = flatternAllT t
flatternAllT t = [t]

extractConstrs t@(Typ (HsTyCon (PNT pn (Type (TypeInfo _ [] _)) _ ))) 
  = error "There are no constructors defined for the type of this pattern!"   
extractConstrs (Typ (HsTyCon (PNT pn (Type (TypeInfo _ cs _)) _ ))) = cs
extractConstrs x = error "Please select a variable with a type constructor!" 


extractConstrs' t@(Typ (HsTyCon (PNT pn (Type (TypeInfo _ [] _)) _ ))) _ _ _ _
  = error "There are no constructors defined for the type of this pattern!" 
extractConstrs' (Typ (HsTyCon (PNT pn (Type (TypeInfo _ cs _)) _ ))) _ _ _ _ = cs
extractConstrs' (Typ (HsTyVar (PNT pn (Type (TypeInfo _ cs _)) _ ))) types ty pos constrName 
   =  -- if it's a variable, then it must be exposed on the
      -- LHS of the type
      -- what about existential types?
      let posOfVar = findPosOfVar constrName ty
          instanceOfVarType = findPosOfInstance posOfVar (declToPNT ty) types
        in extractConstrs instanceOfVarType      

findPosOfInstance _ _ [] = error "pattern is a variable which is not instantiated within the type signature!"
findPosOfInstance offset pn (t@(Typ (HsTyCon pnt)):ts)
 | rmLocs pn == rmLocs pnt = ts !! (offset-1)
 | otherwise               = findPosOfInstance offset pn ts

findPosOfVar (Typ (HsTyVar pnt)) (Dec (HsDataDecl _ _ t _ _))
   = extractPos 0 (flatternAllT t) 
       where
         extractPos i [] = i
         extractPos i ((Typ (HsTyCon pnt2)):ts) 
           = extractPos (i+1) ts
         extractPos i ((Typ (HsTyVar pnt2)):ts)
           | rmLocs pnt2 == rmLocs pnt = i
           | otherwise                 = extractPos (i+1) ts

