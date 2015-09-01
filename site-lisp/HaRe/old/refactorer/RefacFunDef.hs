-----------------------------------------------------------------------------
-- |
-- Module      :  RefacFunDef
-- Copyright   :  (c) Christopher Brown 2005
--
-- Maintainer  :  cmb21@kent.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- This module contains a transformation for HaRe.
-- Function Definition folding.
-- Looks for duplicate code and replaces it with a call to the function.
--   e.g.
--
-- @ square x = x * x @
--
-- @ g x y = x * x + y * y @
--
--   will be refactored to:
--
-- @ square x = x * x @
--
-- @ g x y = square x + square y @
--
-----------------------------------------------------------------------------

module RefacFunDef (
 
   -- ** Data types
   Binding, Environment, NonSetEnv,
   FunctionPats, WhereDecls,
 
   -- * Function types
   subFunctionDef, checkInWhere, checkInPat,
   createFunc, createFunc', getEnvironment,
   canAddBind, checkVal, rewritePatsInEnv,
   doZip, zipHighlightedMatch, callZipHighlightedMatch,
   zipHighlightedField, zipHighlightedStmt,
   -- * Type signatures with argument docs
   findDefNameAndExp 
 
  ) where

import PrettyPrint
import PrettyPrint
import PosSyntax
import AbstractIO
import Data.Maybe
import TypedIds
import UniqueNames hiding (srcLoc)
import PNT
import TiPNT
import Data.List
import RefacUtils
import PFE0 (findFile)
import MUtils (( # ))
import RefacLocUtils
import RefacGenFold hiding (FunctionPats, WhereDecls, Er, Patt, Mat, findDefNameAndExp, PatFun)

-- | Binds an exp to another e.g. (HsID x, HsLit 5) says x is bound to 5.
-- and it continues until the next non-comment line
type Binding = (HsExpP, HsExpP)

-- | An environment is a *set* of bindings.
type Environment = [Binding]

{- | An environment that is not yet a set - should be processed into an
    'Environment'. -}
type NonSetEnv = [Maybe Binding]

-- | An argument list for a function which of course is a list of paterns.
type FunctionPats = [HsPatP]

-- | A list of declarations used to represent a where or let clause.
type WhereDecls = [HsDeclP]


data PatFun = Mat | Patt | Er deriving (Eq, Show)

{- | Function Definition folding.
     This folding takes a function definition, looks for duplicate code and
     replaces it with a call to the function.
     e.g.
     @
         square x = x * x
         g x y = x * x + y * y
     @
     will be refactored to:
     @
         square x = x * x
         g x y = square x + square y
     @
-}
subFunctionDef args
  = do let fileName   = args!!0
           beginRow   = read (args!!1)::Int
           beginCol   = read (args!!2)::Int
           endRow     = read (args!!3)::Int
           endCol     = read (args!!4)::Int
       AbstractIO.putStrLn "subFunctionDef"
       
       (inscps, exps, mod, tokList) <- parseSourceFile fileName
              
       -- Parse the input file.
       -- (inscps, exps, mod, tokList) <- parseSourceFile fileName
                      
       -- Find the function that's been highlighted as the refactree
       let (ty, pnt, pats, subExp, wh)
             = findDefNameAndExp tokList
                                 (beginRow, beginCol)
                                 (endRow, endCol)
                                 mod
       let exp = locToExp (beginRow, beginCol)
                          (endRow, endCol)
                          tokList
                          mod
       {-
        - Do the refactoring!  Returns modifications as below:
        - mod'     - the modified Abstract Syntax Tree
        - tokList' - the modified Token Stream
        - m        - ???
        -}
       if ty == Mat
         then do 
            (mod', ((tokList', m), _)) <- runStateT (doZip pnt wh pats subExp mod)
                                                    ((tokList, False), (0,0))
       
            -- Write out the refactoring
            writeRefactoredFiles False [((fileName, m), (tokList', mod'))]
            AbstractIO.putStrLn "Completed.\n"
         else do
           (mod', ((tokList', m) , _)) <- runStateT (doSubstitution pnt subExp mod) ((tokList,False),( 0, 0))
           writeRefactoredFiles False [((fileName, m), (tokList', mod'))]
           AbstractIO.putStrLn "Completed.\n"



doSubstitution p e
   = applyTP (full_tdTP (idTP `adhocTP` inMod
                              `adhocTP` inMatch
                              `adhocTP` inPat  ))
       where
        inMod (mod@(HsModule loc name exps imps ds):: HsModuleP)
         | p `elem` (map declToPNT ds) 
             = do
                  ds' <- doZipModule ds
                  return (HsModule loc name exps imps ds')
            where
             doZipModule t
              = applyTP (full_tdTP (idTP `adhocTP` inMatch2
                                        `adhocTP` inPat2)) t
               where
               inMatch2 (match@(HsMatch loc name pats rhs ds)::HsMatchP)
                  = do
                    (_, declared) <- hsFreeAndDeclaredNames pats
                    (_, declared') <- hsFreeAndDeclaredNames match
                    (_, declared'') <- hsFreeAndDeclaredNames ds
                    if (pNTtoName p) `elem` (declared++(declared'++declared''))
                      then return match
                      else do  e' <- doSubstitution' p e declared rhs
                               return (HsMatch loc name pats e' ds)
                        

               inPat2 (pat@(Dec (HsPatBind loc pa rhs ds))::HsDeclP)
                 = do
                   (_, declared)  <- hsFreeAndDeclaredNames pat
                   (_, declared') <- hsFreeAndDeclaredNames ds
                   if (pNTtoName p) `elem` (declared++declared')
                    then return pat
                    else do e' <- doSubstitution' p e declared rhs
                            return (Dec (HsPatBind loc pa e' ds))
                
               inPat2 x = return x
               
        inMod x = return x    
        
        inMatch (match@(HsMatch loc name pats rhs ds)::HsMatchP)
         | p `elem` (map declToPNT ds)
            = do
                    (_, declared) <- hsFreeAndDeclaredNames pats
                    (_, declared') <- hsFreeAndDeclaredNames match
                    if (pNTtoName p) `elem` (declared++declared')
                      then return match
                      else do 
                              e' <- doSubstitution' p e declared rhs
                              return (HsMatch loc name pats e' ds)
      
        inMatch x = return x

        inPat (pat@(Dec (HsPatBind loc pa rhs ds))::HsDeclP)
         | p `elem` (map declToPNT ds)
               = do
                   (_, declared)  <- hsFreeAndDeclaredNames pat
                   if (pNTtoName p) `elem` declared
                    then return pat
                    else do e' <- doSubstitution' p e declared rhs
                            return (Dec (HsPatBind loc pa e' ds))
        
        inPat x = return x

           
doSubstitution' p e declared t
    = applyTP (stop_tdTP (failTP `adhocTP` subExp)) t
       where 
         subExp exp@((Exp _)::HsExpP)
          | sameOccurrence exp e == False
               = if toRelativeLocs e == toRelativeLocs exp then update exp (createFunc p) exp
                                                           else mzero
          | otherwise                     
                  = mzero

         createFunc pat = (Exp (HsId (HsVar pat)))            
           

           
           
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
              (applyTU (once_tdTU (failTU `adhocTU` inMatch `adhocTU` inPat)) t)

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
      inPat (pat@(Dec (HsPatBind loc1 ps rhs@(HsBody e) ds))::HsDeclP)
        | locToExp beginPos endPos toks rhs /= defaultExp
          = Just (Patt, patToPNT ps, [], locToExp beginPos endPos toks rhs, ds)
      --The selected sub-expression is in the rhs of a pattern-binding
      inPat (pat@(Dec (HsPatBind loc1 ps rhs@(HsGuard es) ds))::HsDeclP)
        | locToExp beginPos endPos toks rhs /= defaultExp
          = Just (Patt, patToPNT ps, [], rmGuard rhs, ds)
      inPat _ = Nothing

      rmGuard ((HsGuard gs)::RhsP)
             = let (_,e1,e2)=glast "guardToIfThenElse" gs
               in  if ((pNtoName.expToPN) e1)=="otherwise" 
                   then (foldl mkIfThenElse e2 (tail(reverse gs)))
                   else (foldl mkIfThenElse defaultElse (reverse gs)) 
           
      mkIfThenElse e (_,e1, e2)=(Exp (HsIf e1 e2 e)) 

      defaultElse=(Exp (HsApp (Exp (HsId (HsVar (PNT (PN (UnQual "error") (G (PlainModule "Prelude") "error" 
                    (N (Just loc0)))) Value (N (Just loc0)))))) (Exp (HsLit loc0 (HsString "UnMatched Pattern")))))


doZip :: (MonadPlus m, Term t, MonadState (([PosToken],Bool),(Int, Int)) m) => 
         PNT -> WhereDecls -> FunctionPats -> HsExpP -> t
             -> m t
doZip p w patsGlob e t
  = applyTP (full_tdTP (idTP  `adhocTP` inMod
                              `adhocTP` inMatch
                              `adhocTP` inPat  )) t
       where
        inMod (mod@(HsModule loc name exps imps ds):: HsModuleP)
         | p `elem` (map declToPNT ds) 
             = do
                  ds' <- doZipModule ds
                  return (HsModule loc name exps imps ds')
            where
             doZipModule t
              = applyTP (full_tdTP (idTP `adhocTP` inMatch2
                                        `adhocTP` inPat2)) t
               where
               inMatch2 (match@(HsMatch loc name pats rhs ds)::HsMatchP)
                  = do
                    (_, declared) <- hsFreeAndDeclaredNames pats
                    (_, declared') <- hsFreeAndDeclaredNames match
                    (_, declared'') <- hsFreeAndDeclaredNames ds
                    if (pNTtoName p) `elem` (declared++(declared'++declared''))
                      then return match
                      else do e' <- doZip' p w patsGlob e rhs
                              return (HsMatch loc name pats e' ds)
                        

               inPat2 (pat@(Dec (HsPatBind loc pa rhs ds))::HsDeclP)
                 = do
                   (_, declared)  <- hsFreeAndDeclaredNames pat
                   (_, declared') <- hsFreeAndDeclaredNames ds
                   if (pNTtoName p) `elem` (declared++declared')
                    then return pat
                    else do e' <- doZip' p w patsGlob e rhs
                            return (Dec (HsPatBind loc pa e' ds))
                
               inPat2 x = return x
        inMod x = return x
          
         
            
       
       
        inMatch (match@(HsMatch loc name pats rhs ds)::HsMatchP)
         | p `elem` (map declToPNT ds)
            = do
                    (_, declared) <- hsFreeAndDeclaredNames pats
                    (_, declared') <- hsFreeAndDeclaredNames match
                    if (pNTtoName p) `elem` (declared++declared')
                      then return match
                      else do e' <- doZip' p w patsGlob e rhs
                              return (HsMatch loc name pats e' ds)

        inMatch x = return x

        inPat (pat@(Dec (HsPatBind loc pa rhs ds))::HsDeclP)
         | p `elem` (map declToPNT ds)
               = do
                   (_, declared)  <- hsFreeAndDeclaredNames pat
                   if (pNTtoName p) `elem` declared
                    then return pat
                    else do e' <- doZip' p w patsGlob e rhs
                            return (Dec (HsPatBind loc pa e' ds))
        
        inPat x = return x


{-| 
doZip uses Strafunski to traverse each node of the AST and 
then performs the folding on each node.
-}
doZip' :: (MonadPlus m, Term t, MonadState (([PosToken],Bool),(Int, Int)) m) => 
         PNT -> WhereDecls -> FunctionPats -> HsExpP -> t
             -> m t
doZip' p w pats e t
  = applyTP (stop_tdTP (failTP `adhocTP` (zipExpCheck p w pats e))) t
    where
      zipExpCheck p w pats (exp1::HsExpP) (exp2::HsExpP)
        | sameOccurrence exp1 exp2 == False
            = do 
                 result <- (callZipHighlightedMatch pats w exp1 exp2)
                 let environment = getEnvironment result
                 if result == [Nothing] || environment == Nothing
                   then do fail ""
                   else do let Just env = environment
                           let result' = map (rewritePatsInEnv env) pats
                           update exp2 (createFunc p result') exp2
                           
        | otherwise
           = return exp1

{-|
checkVal calls checkAddBind in succession to check that all the bindings
can be added to the environment or not.
 -}
 
checkVal :: NonSetEnv -> Bool
checkVal xs
  = checkValAux xs []
    where
      checkValAux :: NonSetEnv -> Environment -> Bool
      checkValAux [] _ = True
      checkValAux ((Just (x,y)) : xs) env
        = canAddBind (x,y) env &&
          checkValAux xs ((x,y):env)
      checkValAux (Nothing:xs) env = checkValAux xs env

{-|
canAddBind takes a binding and some environments, and checks to see
whether the binding can be added to the environment or not.
The binding will not be added to the environment if that binding
already exists within the environment. canAddBind returns True
if the binding can be added, and False if it cannot.
-}

canAddBind :: Binding -> Environment -> Bool
canAddBind _ [] = True
canAddBind (x,y) ((x',y'):xs)
  = (x1 == x1' && y1 == y1') ||
    (x1 /= x1' && canAddBind (x,y) xs)
    where
      [x1,x1',y1,y1'] = map toRelativeLocs [x,x',y,y']

{-|
getEnvironment takes a list of bindings and removes
the duplicates within the bindings
-}

getEnvironment :: NonSetEnv -> Maybe Environment
getEnvironment [] = Just []
getEnvironment (Nothing: xs) = getEnvironment xs
getEnvironment (Just (x,y):xs)
  = case subEnv of
      Nothing  -> Nothing
      Just env -> if canAddBind (x,y) env
                    then Just ((x,y):env)
                    else Nothing
    where
      subEnv = getEnvironment xs


{-|
rewritePatsInEnv takes the Environment and a pattern belonging to the
argument list of the function the user is folding against.
rewritePatsInEnv then forms an expression based on this pattern
taking into consideration the environment. This is used when forming
the function call
e.g.
@
  Environment = [("x", [1,2,3]), ("y", 1)]
  pat = (x,y) 
@

would return...

@
  HsTuple ([1,2,3], 1)
@
  
-}

rewritePatsInEnv :: Environment -> HsPatP -> HsExpP
rewritePatsInEnv [] p = error "Empty Environment!"
rewritePatsInEnv env (pat1@(Pat (HsPRec x y)))
  = Exp (HsRecConstr loc0 x (map (sortField env) y))
    where
      sortField :: Environment -> HsFieldI a HsPatP -> HsFieldI a HsExpP
      sortField env (HsField i e) = (HsField i (rewritePatsInEnv env e))

rewritePatsInEnv env (pat1@(Pat (HsPLit x y)))
  = Exp (HsLit x y)

rewritePatsInEnv env (pat1@(Pat (HsPAsPat i p1)))
  = Exp (HsAsPat i (rewritePatsInEnv env p1))

rewritePatsInEnv env (pat1@(Pat (HsPIrrPat p1)))
  = Exp (HsIrrPat (rewritePatsInEnv env p1))

rewritePatsInEnv env (pat1@(Pat (HsPWildCard)))
  = nameToExp "undefined"

rewritePatsInEnv env (pat1@(Pat (HsPApp i p1)))
  = createFunc i (map (rewritePatsInEnv env) p1)

rewritePatsInEnv env (pat1@(Pat (HsPList _ p1)))
  = Exp (HsList (map (rewritePatsInEnv env) p1))

rewritePatsInEnv env (pat1@(Pat (HsPTuple _ p1)))
  = Exp (HsTuple (map (rewritePatsInEnv env) p1))

rewritePatsInEnv env (pat1@(Pat (HsPInfixApp p1 x p2)))
  =  Exp (HsInfixApp (rewritePatsInEnv env p1)
                     (HsCon x)
                     (rewritePatsInEnv env p2))

rewritePatsInEnv env (pat@(Pat (HsPParen p1)))
  = Exp (HsParen (rewritePatsInEnv env p1))

rewritePatsInEnv env (pat1@(Pat (HsPId (HsVar (PNT (PN (UnQual i) _) _ _)))))
  = if findRewrites i == []
      then nameToExp "undefined"
      else snd (head (findRewrites i))
    where
      findRewrites i = filter (checkPat i) env
      checkPat i (Exp (HsId (HsVar (PNT (PN (UnQual i2) _) _ _))), (Exp z))
        = i == i2
      checkPat i _ = False

{-|
callZipHighlightedMatch simply calls the function zipHighlightedMatch
and then returns the value wrapped in a monad
-}
callZipHighlightedMatch :: Monad m =>  FunctionPats -> WhereDecls 
                         -> HsExpP -> HsExpP -> m NonSetEnv
callZipHighlightedMatch pats w (exp1::HsExpP) (exp2::HsExpP)
  = do zippedE1 <- zipHighlightedMatch False pats w exp1 exp2
       return zippedE1

{- |
zipHighlightedMatch takes a list of patterns (the list of arguments for the 
function highlighted, the where clause associated with the function, 
the expression that has been highlighted and the expression that we are trying
to fold against.
   
zipHighlightedMatch then checks to see if the the expressions can be paired.
The expressions will only be paired if:
both expressions have the ssame type
e.g.
      refactoron -> [1,2,3,4]
      refactorod -> [1,2,3,4] becomes ([1,2,3,4], [1,2,3,4])
        
or, the highlighted expression is an idenitfier, in which case a pair is
always created, unless the idenitifier does not appear in the argument list
(pats)
  
-}

zipHighlightedMatch :: Monad m => Bool ->  FunctionPats -> WhereDecls 
                    -> HsExpP -> HsExpP -> m NonSetEnv
zipHighlightedMatch b pats w (exp1@(Exp (HsId (HsCon i1)))::HsExpP)
                             (exp2@(Exp (HsId (HsCon i2)))::HsExpP)
  | i1 == i2  = return [ Just (exp1, exp2) ]
  | otherwise = return [ Nothing ]
zipHighlightedMatch b pats w (exp1@(Exp (HsId (HsCon i1)))::HsExpP)
                             (exp2::HsExpP)
  = return [ Nothing ]
zipHighlightedMatch True pats w (exp1@(Exp (HsId i1))::HsExpP) 
                           (exp2@(Exp (HsId i2))::HsExpP)
  | not (checkDefs i1 i2) = fail "untouched"      
  | checkInPat pats exp2 = return  [ Just (exp1, exp2) ]
--  | checkInPat pats exp1  = return [ Just (exp1, exp2) ]
  | checkGlobal i1 i2     = return [ Just (exp1, exp2) ]
  | not (checkInWhere w exp1) = return [Nothing]
  | otherwise                 = fail "untouched"
    where
     checkGlobal (HsVar i1) (HsVar i2) = (pNTtoPN i1) == (pNTtoPN i2)
     checkGlobal _ _ = False
zipHighlightedMatch False pats w (exp1@(Exp (HsId i1))::HsExpP) 
                                 (exp2@(Exp (HsId i2))::HsExpP)

  | checkInPat pats exp1  = return [ Just (exp1, exp2) ]
  | checkGlobal i1 i2     = return [ Just (exp1, exp2) ]
  | not (checkInWhere w exp1) = return [Nothing]
  | otherwise                 = fail "untouched"
    where
     checkGlobal (HsVar i1) (HsVar i2) = (pNTtoPN i1) == (pNTtoPN i2)
     checkGlobal _ _ = False
zipHighlightedMatch b pats w (exp1@(Exp (HsId i))::HsExpP) (exp2::HsExpP)
  | checkInPat pats exp1 == True &&
    checkInWhere w exp1 /= True
      = return [ Just (exp1, exp2) ]
  | otherwise
      = fail "untouched" 

zipHighlightedMatch b pats w (exp1@(Exp (HsLit _ i1))::HsExpP)
                             (exp2@(Exp (HsLit _ i2))::HsExpP)
  | i1 == i2  = return [ Just (exp1, exp2) ]
  | otherwise = return [ Nothing ]

zipHighlightedMatch b pats w (exp1@(Exp (HsLit _ _))::HsExpP) (exp2::HsExpP)
  = return [Nothing]

zipHighlightedMatch b pats w (exp1@(Exp (HsInfixApp e1 i e2))::HsExpP)
              (exp2@(Exp (HsInfixApp e11 i2 e22))::HsExpP)
  | i == i2   = do zippedE1 <- zipHighlightedMatch b pats w e1 e11
                   zippedE2 <- zipHighlightedMatch b pats w e2 e22
                   if zippedE1 == [ Nothing ] || zippedE2 == [ Nothing ]
                     then return [ Nothing ]
                     else return (zippedE1 ++ zippedE2)
  | otherwise = return [ Nothing ]


zipHighlightedMatch b pats w (exp1@(Exp (HsInfixApp e1 i e2))::HsExpP) 
                           (exp2::HsExpP)
  = return [Nothing]

zipHighlightedMatch b pats w (exp1@(Exp (HsApp e1 e2))::HsExpP)
                             (exp2@(Exp (HsApp e11 e22))::HsExpP)
  = do zippedE1 <- zipHighlightedMatch b pats w e1 e11
       zippedE2 <- zipHighlightedMatch b pats w e2 e22
       if zippedE1 == [Nothing] || zippedE2 == [ Nothing ]
         then return [Nothing]
         else return (zippedE1 ++ zippedE2)

zipHighlightedMatch b pats w (exp1@(Exp (HsApp e1 e2))::HsExpP) (exp2::HsExpP)
  = return [Nothing]

zipHighlightedMatch b pats w (exp1@(Exp (HsNegApp _ e1))::HsExpP)
              (exp2@(Exp (HsNegApp _ e2))::HsExpP)
  = do zippedE1 <- zipHighlightedMatch b pats w e1 e2
       return zippedE1

zipHighlightedMatch b pats w (exp1@(Exp (HsNegApp _ e1))::HsExpP) (exp2::HsExpP)
  = return [Nothing]

zipHighlightedMatch b pats w (exp1@(Exp (HsLambda ps e1))::HsExpP)
                           (exp2@(Exp (HsLambda ps2 e11))::HsExpP) 
 | wildCardAllPNs ps == wildCardAllPNs ps2
     = do zippedE1 <- zipHighlightedMatch b pats w e1 (localRewriteExp e11 (localRewritePats ps ps2))
          return zippedE1
        where
         localRewritePats [] ps = []
         localRewritePats ps [] = []
         localRewritePats (p1:p1s) (p2:p2s) 
           = (rewritePat p2 p1) : (localRewritePats p1s p2s)
        
         localRewriteExp e [] = e   
         localRewriteExp e (p1:p1s)
           = let e1' = rewritePatsInExp p1 e  in localRewriteExp e1' p1s
zipHighlightedMatch b pats w (exp1@(Exp (HsLet _ e1))::HsExpP)
              (exp2@(Exp (HsLet _ e11))::HsExpP)
  = do zippedE1 <- zipHighlightedMatch b pats w e1 e11
       return zippedE1

zipHighlightedMatch b pats w (exp@(Exp (HsLet _ e1))::HsExpP) (exp2::HsExpP)
  = fail ""

zipHighlightedMatch b pats w (exp1@(Exp (HsLambda _ e1))::HsExpP) (exp2::HsExpP)
  = return [Nothing]

zipHighlightedMatch b pats w (exp1@(Exp (HsIf e1 e2 e3))::HsExpP)
              (exp2@(Exp (HsIf e11 e22 e33))::HsExpP)
  = do zippedE1 <- zipHighlightedMatch b pats w e1 e11
       zippedE2 <- zipHighlightedMatch b pats w e2 e22
       zippedE3 <- zipHighlightedMatch b pats w e3 e33
       return (zippedE1 ++ zippedE2 ++ zippedE3)

zipHighlightedMatch b pats w (exp1@(Exp (HsIf e1 e2 e3))::HsExpP) (exp2::HsExpP)
  = return [Nothing]

zipHighlightedMatch b pats 
                    w 
                    (exp1@(Exp (HsCase e1 (alt@(HsAlt _ p1 e2 ds1):alts1)))::HsExpP)
                    (exp2@(Exp 
                              (HsCase e11 
                                         (alt2@(HsAlt _ p11 e22 ds11):alts2)
                              ))::HsExpP)
  = do zippedE1 <- zipHighlightedMatch b pats w e1 e11
       res <- zippedAlts (alt:alts1) (alt2:alts2)
       if res == [Nothing] 
          then return [Nothing]
          else return (zippedE1 ++ res)
         where
           zippedAlts [] alts = return []
           zippedAlts alts [] = return []
           zippedAlts ((HsAlt _ p1 (HsBody exp1) ds1):alts1) ((HsAlt _ p11 (HsBody exp2) ds11):alts2)
             | wildCardAllPNs p1 == wildCardAllPNs p11
             = do
                  zippedE1 <- zipHighlightedMatch b pats w exp1 (rewritePatsInExp (rewritePat p11 p1) exp2)
                  if zippedE1 == [Nothing]
                    then return [Nothing]
                    else do res <- zippedAlts alts1 alts2
                            if res == [Nothing] then return [Nothing]
                                                else return (zippedE1 ++ res)
             | otherwise = return [Nothing]
           zippedAlts ((HsAlt _ p1 (HsGuard g1) ds1):alts1) ((HsAlt _ p22 (HsGuard g2) ds11):alts2)
             | wildCardAllPNs p1 == wildCardAllPNs p22
               = do
                    zippedE1 <- zippedGuards g1 (rewritePatsInGuard (rewritePat p22 p1) g2)
                    -- error $ show zippedE1
                    if zippedE1 == [Nothing]
                      then return [Nothing]
                      else do
                              res <- zippedAlts alts1 alts2
                              if res == [Nothing] then return [Nothing]
                                                  else return (zippedE1 ++ res)
                where
                  zippedGuards _ [] = return []
                  zippedGuards [] _ = return []
                  zippedGuards ((_, e1, e2):gs1) ((_, e3, e4):gs2)
                    = do
                         e1' <- zipHighlightedMatch True pats w e1 e3
                         e2' <- zipHighlightedMatch True pats w e2 e4
                         res <- zippedGuards gs1 gs2
                         return ((e1' ++ e2') ++ res)
           zippedAlts _ _ = return [Nothing]
zipHighlightedMatch b pats w (exp1@(Exp 
                                     (HsCase e1 
                                               ((HsAlt _ e2 p1 ds1):alts1)
                                     ))::HsExpP)
                           (exp2::HsExpP)
                
  = return [Nothing]

zipHighlightedMatch b pats w (exp1@(Exp (HsDo (stat1)))::HsExpP)
                             (exp2@(Exp (HsDo (stat2)))::HsExpP) 
  = do zippedE1 <- zipHighlightedStmt pats w stat1 stat2
       return zippedE1

zipHighlightedMatch b pats w (exp1@(Exp (HsDo (stat1)))::HsExpP) (exp2::HsExpP)
  = return [Nothing]
  
zipHighlightedMatch b pats w (exp1@(Exp (HsTuple ([e1])))::HsExpP)
                           (exp2@(Exp (HsTuple ([e11])))::HsExpP)
  = do zippedE1 <- zipHighlightedMatch b pats w e1 e11
       return zippedE1

zipHighlightedMatch b pats w (exp1@(Exp (HsTuple (e1:e1s)))::HsExpP)
                             (exp2@(Exp (HsTuple (e11:e11s)))::HsExpP)
  = do zippedE1 <- zipHighlightedMatch b pats w e1 e11
       result <- zippedE2 e1s e11s
       if result == [Nothing] || zippedE1 ==  [Nothing]
         then return [Nothing]
         else return (zippedE1 ++ result)
       where
         zippedE2 [] [] = return []
         zippedE2 _ [] = return [Nothing]
         zippedE2 [] _ = return [Nothing]
         zippedE2 (x:xs) (y:ys)
          = do result1 <- zipHighlightedMatch b pats w x y
               result2  <- zippedE2 xs ys
               if result1 == [Nothing] || result2 == [Nothing]
                 then return [Nothing]
                 else return (result1 ++ result2)

zipHighlightedMatch b pats w (exp1@(Exp (HsTuple (e1:e1s)))::HsExpP) 
                           (exp2::HsExpP)
  = return [Nothing]

zipHighlightedMatch b pats w (exp1@(Exp (HsList ([e1])))::HsExpP)
                           (exp2@(Exp (HsList ([e11])))::HsExpP)
  = do zippedE1 <- zipHighlightedMatch b pats w e1 e11
       return zippedE1

zipHighlightedMatch b pats w (exp1@(Exp (HsList (e1:e1s)))::HsExpP)
                           (exp2@(Exp (HsList (e11:e11s)))::HsExpP)
  = do zippedE1 <- zipHighlightedMatch b pats w e1 e11
       result   <- zippedE2 e1s e11s
       -- error (show zippedE1 ++ " " ++ show result)
       if result == [Nothing] || zippedE1 == [Nothing]
         then return [Nothing]
         else return (zippedE1 ++ result)
       where
         zippedE2 [] [] = return []
         zippedE2 _ [] = return [Nothing]
         zippedE2 [] _ = return [Nothing]
         zippedE2 (x:xs) (y:ys) = do
         result1 <- zipHighlightedMatch b pats w x y
         result2  <- zippedE2 xs ys
         if result1 == [Nothing] || result2 == [Nothing] 
           then return [Nothing]
           else return (result1 ++ result2)

zipHighlightedMatch b pats w (exp1@(Exp (HsList (e1:e1s)))::HsExpP) (exp2::HsExpP)
  = return [Nothing]

zipHighlightedMatch b pats w (exp1@(Exp (HsParen e1))::HsExpP)
                             (exp2@(Exp (HsParen e11))::HsExpP)
  = do zippedE1 <- zipHighlightedMatch b pats w e1 e11
       return zippedE1

zipHighlightedMatch b pats w (exp1@(Exp (HsParen e1))::HsExpP) (exp2::HsExpP)
  = do zippedE1 <- zipHighlightedMatch b pats w e1 exp2
       return zippedE1
zipHighlightedMatch b pats w (exp1::HsExpP) (exp2@(Exp (HsParen e2))::HsExpP)
  = do zippedE1 <- zipHighlightedMatch b pats w exp1 e2
       return zippedE1
zipHighlightedMatch b pats w (exp1@(Exp (HsLeftSection e1 i1))::HsExpP)
              (exp2@(Exp (HsLeftSection e11 i2))::HsExpP)
  | i1 == i2  = do zippedE1 <- zipHighlightedMatch b pats w e1 e11
                   return zippedE1
  | otherwise = return [Nothing]

zipHighlightedMatch b pats w (exp1@(Exp (HsLeftSection e1 i1))::HsExpP)
              (exp2::HsExpP)
  = return [Nothing]

zipHighlightedMatch b pats w (exp1@(Exp (HsRightSection i1 e1))::HsExpP)
              (exp2@(Exp (HsRightSection i2 e11))::HsExpP)
  | i1 == i2  = do zippedE1 <- zipHighlightedMatch b pats w e1 e11
                   return zippedE1
  | otherwise = return [Nothing]

zipHighlightedMatch b pats w (exp1@(Exp (HsRightSection i1 e1))::HsExpP)
              (exp2::HsExpP)
  = return [Nothing]

zipHighlightedMatch b pats w (exp1@(Exp (HsRecConstr _ i1 i2 ))::HsExpP)
              (exp2@(Exp (HsRecConstr _ i11 i22 ))::HsExpP)
  | i1 == i11 = do zippedE1 <- zipHighlightedField pats w i2 i22
                   return zippedE1
  | otherwise = do return [Nothing]

zipHighlightedMatch b pats w (exp1@(Exp (HsRecConstr _ i1 i2))::HsExpP) 
                           (exp2::HsExpP)
  = return [Nothing]

zipHighlightedMatch b pats w (exp1@(Exp (HsRecUpdate _ e1 i1))::HsExpP)
              (exp2@(Exp (HsRecUpdate _ e11 i11))::HsExpP)
  = do zippedE1 <- zipHighlightedMatch b pats w e1 e11
       zippedE2 <- zipHighlightedField pats w i1 i11
       return (zippedE1 ++ zippedE2)

zipHighlightedMatch b pats w (exp1@(Exp (HsRecUpdate _ e1 i1))::HsExpP)
                           (exp2::HsExpP)
  = return [Nothing]

zipHighlightedMatch b pats w (exp1@(Exp (HsEnumFrom e1))::HsExpP)
              (exp2@(Exp (HsEnumFrom e11))::HsExpP)
  = do zippedE1 <- zipHighlightedMatch b pats w e1 e11
       return zippedE1

zipHighlightedMatch b pats w (exp1@(Exp (HsEnumFrom e1))::HsExpP) (exp2::HsExpP)
  = return [Nothing]

zipHighlightedMatch b pats w (exp1@(Exp (HsEnumFromTo e1 e2))::HsExpP)
              (exp2@(Exp (HsEnumFromTo e11 e22))::HsExpP)
  = do zippedE1 <- zipHighlightedMatch b pats w e1 e11
       zippedE2 <- zipHighlightedMatch b pats w e2 e22
       return (zippedE1 ++ zippedE2)

zipHighlightedMatch b pats w (exp1@(Exp (HsEnumFromTo e1 e2))::HsExpP) 
                           (exp2::HsExpP)
  = return [Nothing]

zipHighlightedMatch b pats w (exp1@(Exp (HsEnumFromThen e1 e2))::HsExpP)
              (exp2@(Exp (HsEnumFromThen e11 e22))::HsExpP)
  = do zippedE1 <- zipHighlightedMatch b pats w e1 e11
       zippedE2 <- zipHighlightedMatch b pats w e2 e22
       return (zippedE1 ++ zippedE2)

zipHighlightedMatch b pats w (exp1@(Exp (HsEnumFromThen e1 e2))::HsExpP) 
                           (exp2::HsExpP)
  = return [Nothing]

zipHighlightedMatch b pats w (exp1@(Exp (HsEnumFromThenTo e1 e2 e3))::HsExpP)
              (exp2@(Exp (HsEnumFromThenTo e11 e22 e33))::HsExpP)
  = do zippedE1 <- zipHighlightedMatch b pats w e1 e11
       zippedE2 <- zipHighlightedMatch b pats w e2 e22
       zippedE3 <- zipHighlightedMatch b pats w e3 e33
       return (zippedE1 ++ zippedE2 ++ zippedE3)

zipHighlightedMatch b pats w (exp1@(Exp (HsEnumFromThenTo e1 e2 e3))::HsExpP) 
                           (exp2::HsExpP)
  = return [Nothing]

zipHighlightedMatch b pats w (exp1@(Exp (HsListComp (stat1)))::HsExpP)
              (exp2@(Exp (HsListComp (stat2)))::HsExpP)
  = do zippedE1 <- zipHighlightedStmt  pats w stat1 stat2
       return [Nothing]

zipHighlightedMatch b pats w (exp1@(Exp (HsListComp (stat1)))::HsExpP)
                           (exp2::HsExpP)
  = return [Nothing]

zipHighlightedMatch b pats w (exp1@(Exp (HsExpTypeSig _ e1 c1 t1))::HsExpP)
              (exp2@(Exp (HsExpTypeSig _ e2 c2 t2))::HsExpP)
  = do zippedE1 <- zipHighlightedMatch b pats w e1 e2
       return zippedE1

zipHighlightedMatch b pats w (exp1@(Exp (HsExpTypeSig _ e1 c1 t1))::HsExpP)
              (exp2::HsExpP)
  = return [Nothing]

zipHighlightedMatch b pats w (exp1@(Exp (HsAsPat i1 e1))::HsExpP)
              (exp2@(Exp (HsAsPat i11 e11))::HsExpP)
  | i1 == i11 = do zippedE1 <- zipHighlightedMatch b pats w e1 e11
                   return zippedE1
  | otherwise = return [Nothing]

zipHighlightedMatch b pats w (exp1@(Exp (HsAsPat i1 e1))::HsExpP) (exp2::HsExpP)
  = return [Nothing]

zipHighlightedMatch b pats w (exp1@(Exp (HsIrrPat e1))::HsExpP)
              (exp2@(Exp (HsIrrPat e11))::HsExpP)
  = do zippedE1 <- zipHighlightedMatch b pats w e1 e11
       return zippedE1

zipHighlightedMatch b pats w (exp1@(Exp (HsIrrPat e1))::HsExpP) (exp2::HsExpP)
  = return [Nothing]

zipHighlightedMatch b pats w (exp1::HsExpP) (exp2::HsExpP)
  = return [Nothing]

{-|
zipHighlightedField takes the highlighted expression
, and takes the expression that we are folding against.
If they are both fields, it then calls zipHiglightedMatch to
pair up the expressions within the fields.
-}
zipHighlightedField :: Monad m =>  FunctionPats -> WhereDecls 
                    -> HsFieldsI PNT (HsExpI PNT) -> HsFieldsI PNT (HsExpI PNT)
                    -> m NonSetEnv
zipHighlightedField pats w [] _
  = return [Nothing]

zipHighlightedField pats w _ []
  = return [Nothing]

zipHighlightedField pats w ((fiel1@(HsField i1 e1)):xs)
                  ((fiel2@(HsField i11 e11)):ys)
  = if i1 == i11
      then do zippedE1 <- zipHighlightedMatch False pats w e1 e11
              return zippedE1
      else do
              return [Nothing]

checkDefs (HsVar p1@(PNT (PN (UnQual i) (_) ) _ _ )) (HsVar p2@(PNT (PN (UnQual i2) (_) ) _ _ ))
 = i == i2
checkDefs _ _ = False


{-|
checkInPat checks that the Expression (supplied as 2nd argument) 
occurs within the Function Arugment List.
checkInPat needs to check for every case that expression could be
e.g. literals, lists, tuples and records.
if the expression occurs then the function returns True
otherwise returns False.  
-}
   
checkInPat :: FunctionPats -> HsExpP -> Bool
checkInPat (pat1@(Pat (HsPRec x y)):pats) exp
  | (checkField y) == False = (checkInPat pats exp)
  | otherwise               = True
  where
    checkField ((HsField i e):xs)
      | (checkInPat [e] exp) == False = (checkField xs)
      | otherwise                     = True

checkInPat (pat1@(Pat (HsPIrrPat p)):pats) exp
  | (checkInPat [p] exp) == False = checkInPat pats exp
  | otherwise                     = True

checkInPat (pat1@(Pat (HsPAsPat i p)):pats) exp
  | (checkInPat [p] exp) == False = checkInPat pats exp
  | otherwise                     = True

checkInPat (pat1@(Pat (HsPWildCard)):pats) exp
  = checkInPat pats exp

checkInPat (pat1@(Pat (HsPId (HsVar (PNT p@(PN (UnQual i) (_) ) _ _ )))):pats)
           (exp1@(Exp (HsId (HsVar (PNT p2@(PN (UnQual i2) (_) ) _ _ ))))::HsExpP)
 = if p == p2 then True else checkInPat pats exp1
 {- = if i == i2
      then True
      else checkInPat pats exp1 -}

checkInPat (pat1@(Pat (HsPParen pat)):pats) exp
  | (checkInPat [pat] exp) == False = checkInPat pats exp
  | otherwise                       = True

checkInPat (pat@(Pat (HsPInfixApp pat1 x pat2)):pats) exp
  | (checkInPat [pat1] exp) == False &&
    (checkInPat [pat2] exp) == False
              = checkInPat pats exp
  | otherwise = True

checkInPat (pat@(Pat (HsPTuple _ pat1)):pats) exp
  | (checkInPat pat1 exp) == False = checkInPat pats exp
  | otherwise                      = True

checkInPat (pat@(Pat (HsPList _ pat1)):pats) exp
  | (checkInPat pat1 exp) == False = checkInPat pats exp
  | otherwise                      = True

checkInPat (pat@(Pat (HsPApp i pat1)):pats) exp
  | (checkInPat pat1 exp) == False = checkInPat pats exp
  | otherwise                      = True

checkInPat ((Pat (HsPLit _ (HsInt x))):pats) exp1
  = checkInPat pats exp1
checkInPat _ _ = False


{-|
checkInWhere checks that where clause of the function does not contain
the expressions (as second argument). If it does the function returns
True, otherwise returns False. 
-}

checkInWhere :: [HsDeclP] -> HsExpP -> Bool
checkInWhere [] _ = False
checkInWhere (wh@(Dec
                   (HsPatBind _
                              (Pat
                                (HsPId
                                  (HsVar
                                    (PNT
                                      (PN
                                        (UnQual i)
                                        _
                                      )
                                      _
                                      _
                                    )
                                  )
                                )
                              )
                              _
                              rest)):ws)
             (exp1@(Exp (HsId (HsVar (PNT (PN (UnQual i2) _ ) _ _ ))))::HsExpP)
  = i == i2 
  
-- extractHsBody simply extracts the expression within an HsBody
-- and returns that Expression.
extractHsBody (HsBody exp) = return exp
extractHsBody _ = error "Case must contain HsBody"

{-|
zipHighLightedStmt checks that two statements are identical,
if they are, zipHighLightedStmt returns the two statements paired together
-}

zipHighlightedStmt :: Monad m =>  FunctionPats -> WhereDecls 
                    -> HsStmtP -> HsStmtP -> m NonSetEnv
zipHighlightedStmt pats w (exp1@(HsGenerator _ p1 e1 e1')::HsStmtP)
                          (exp2@(HsGenerator _ p2 e2 e2')::HsStmtP)
 | wildCardAllPNs p1 == wildCardAllPNs p2 
  = do zippedE1 <- zipHighlightedMatch False pats w e1 e2
       zippedE2 <- zipHighlightedStmt pats w e1' e2'
       return (zippedE1 ++ zippedE2)

zipHighlightedStmt pats w (exp1@(HsQualifier e1 e1')::HsStmtP)
                          (exp2@(HsQualifier e2 e2')::HsStmtP)
  = do zippedE1 <- zipHighlightedMatch False pats w e1 e2
       zippedE2 <- zipHighlightedStmt pats w e1' e2'
       return [Nothing]

zipHighlightedStmt pats w (exp1@(HsLetStmt ds1 e1)::HsStmtP)
                          (exp2@(HsLetStmt ds2 e2)::HsStmtP)
  = do zippedE1 <- zipHighlightedStmt pats w e1 e2
       return zippedE1

zipHighlightedStmt pats w (exp1@(HsLast e1)::HsStmtP)
                          (exp2@(HsLast e2)::HsStmtP)
  = do zippedE1 <- zipHighlightedMatch False pats w e1 e2
       return zippedE1

zipHighlightedStmt pats w (exp1::HsStmtP) (exp2::HsStmtP)
  = return [Nothing]

