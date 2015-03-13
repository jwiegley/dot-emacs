-----------------------------------------------------------------------------
-- |
-- Module      :  RefacAsPatterns
-- Copyright   :  (c) Christopher Brown 2007
--
-- Maintainer  :  cmb21@kent.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- This module contains a transformation for HaRe.
-- Convert all patterns into AS patterns and 
-- change all reference to the pattern on the RHS to references
-- to the AS name.
--
-----------------------------------------------------------------------------

module RefacAsPatterns where


import System.IO.Unsafe
import PrettyPrint
import RefacTypeSyn
import RefacLocUtils
import Data.Char
import GHC.Unicode
import AbstractIO
import Data.Maybe
import Data.List
import RefacUtils

data Patt = Match HsMatchP | MyAlt HsAltP | MyDo HsStmtP | MyListComp HsExpP
             deriving (Show)
refacAsPatterns args
  = do let 
           fileName    = args!!0
           name        = args!!1
           beginRow    = read (args!!2)::Int
           beginCol    = read (args!!3)::Int
           endRow      = read (args!!4)::Int
           endCol      = read (args!!5)::Int

       AbstractIO.putStrLn "refacAsPatterns"

       unless (isVarId name) 
                  $ error "The new name is invalid!\n"


       -- Parse the input file.
       modInfo@(inscps, exps, mod, tokList) <- parseSourceFile fileName
       
       -- there are two modes to this refactoring:
       -- either one selects a pattern, or, one selects an expression (referring to a pattern).
       
       let exp = locToExp (beginRow, beginCol) (endRow, endCol) tokList mod
       
       case exp of
         Exp (HsId (HsVar (PNT (PN (UnQual "unknown") (G (PlainModule "unknown") "--" (N Nothing))) Value  (N Nothing)) ))
           -> do
       
                let (pnt, pat, match) = findPattern tokList (beginRow, beginCol) (endRow, endCol) mod
                                
                ((_,m), (newToks, newMod)) <- applyRefac (changePattern name pat match) (Just (inscps, exps, mod, tokList)) fileName
       
                unless (newMod /= mod) $ AbstractIO.putStrLn "Pattern does not occur on the rhs!"
  
                writeRefactoredFiles False [((fileName, m), (newToks, newMod))]   
                AbstractIO.putStrLn "Completed.\n"
         _
           -> do
                 -- all we need is the expression and the pattern to which it is imitating...
                 
                 let pat = getPat exp mod
                 
                 ((_,m), (newToks, newMod)) <- applyRefac (changePatternSimple name pat exp) (Just (inscps, exps, mod, tokList)) fileName
                 
                 writeRefactoredFiles False [((fileName, m), (newToks, newMod))]
                 AbstractIO.putStrLn "Completed.\n"
          

getPat exp t
 = fromMaybe (error "No Pattern is associated with the highlighted expression!")
     (applyTU (once_tdTU (failTU `adhocTU` worker)) t)
       where
        worker (p :: HsPatP) 
          | rewritePats p == exp = Just p
          | otherwise = Nothing


convertPat :: String -> HsPatP -> HsPatP
convertPat _ (Pat (HsPAsPat n p)) = error "The selected pattern is already an as-pattern!"
convertPat _ (Pat (HsPId _)) = error "Cannot perform to-as-patterns on a simple variable!"
convertPat _ (Pat (HsPLit _ _)) = error "Cannot perform to-as-patterns on a constant value!"
convertPat name (Pat (HsPParen p)) = convertPat name p
convertPat name p = (Pat (HsPAsPat (nameToPNT name) p))

changePatternSimple name pat exp (_, _, t)
 = do

       inscopeNames <- hsVisibleNames exp t
       unless (not (name `elem` inscopeNames))
        $ error ("the use of the name: " ++ name ++ " is already in scope!")
       
       -- let newPats = checkPats name pat [p]
       let convertedPat = convertPat name pat
       newExp <- checkExpr convertedPat exp

       newT <- update exp newExp t
       newT2 <- update pat convertedPat newT
       
       return newT2



changePattern name pat (Match match) (_, _,t)
  = do 
       newDecl <- lookInMatches t name pat [match]
       newT <- update match (newDecl !! 0) t
       return newT

changePattern name pat (MyAlt alt) (_, _, t)
  = do
       newAlt <- lookInAlt t name pat alt
       newT <- update alt newAlt t
       return newT
       
changePattern name pat (MyDo inDo) (_,_, t)
  = do
       newDo <- lookInDo t name pat inDo
       newT <- update inDo newDo t
       return newT
       
changePattern name pat (MyListComp inList) (_,_,t)
 = do
       newList <- lookInList t name pat inList
       newT <- update inList newList t
       return newT

-- sconvertPatterns :: (Term t, MonadPlus m,Monad m) => t -> String -> HsPatP -> HsDeclP -> m HsDeclP
convertPatterns t name pat dec@(Dec (HsPatBind a b (HsBody e) ds)) 
  = do
        newExp <- checkExpr (Pat (HsPAsPat (nameToPNT name) pat)) e
        return (Dec (HsPatBind a b (HsBody newExp) ds))
convertPatterns t name pat (Dec (HsFunBind loc matches)) 
  = 
    do
       rest <- lookInMatches t name pat matches
       return (Dec (HsFunBind loc  rest ))

lookInMatches _ _ _ []  = return []
lookInMatches t name pat (match@(HsMatch s pnt (p:ps) (HsGuard g@((_,_,e):gs)) ds):ms)
    = do       
       inscopeNames <- hsVisibleNames e t
       unless (not (name `elem` inscopeNames))
        $ error ("the use of the name: " ++ name ++ " is already in scope!")
    
       let newPats = checkPats name pat (p:ps)
       let convertedPat = convertPat name pat
       newGuard <- checkGuards convertedPat g
       newDS <- mapM (convertPatterns t name pat) ds
       rest <- lookInMatches t name pat ms
       if newGuard == g && newDS == ds
         then do
           return (HsMatch s pnt (p:ps) (HsGuard g) ds : rest)
         else do
           return (HsMatch s pnt newPats (HsGuard newGuard) newDS : rest)

         
lookInMatches t name pat (match@(HsMatch s pnt (p:ps) (HsBody e) ds):ms)
   = do
       inscopeNames <- hsVisibleNames e t
       unless (not (name `elem` inscopeNames))
        $ error ("the use of the name: " ++ name ++ " is already in scope!")
       
       let newPats = checkPats name pat (p:ps)
       let convertedPat = convertPat name pat
       newExp <- checkExpr convertedPat e
       newDS <- mapM (convertPatterns t name pat) ds
       rest <- lookInMatches t name pat ms
       if newExp == e && newDS == ds
         then do
           return (HsMatch s pnt (p:ps) (HsBody e) ds : rest)     
         else do
           return (HsMatch s pnt newPats (HsBody newExp) newDS : rest)


lookInAlt t name pat (alt@(HsAlt s p (HsGuard g@((_,_,e):gs))  ds)::HsAltP)
    = do       
       inscopeNames <- hsVisibleNames e t
       unless (not (name `elem` inscopeNames))
        $ error ("the use of the name: " ++ name ++ " is already in scope!")
    
       let newPats = checkPats name pat [p]
       let convertedPat = convertPat name pat
       newGuard <- checkGuards convertedPat g
       newDS <- mapM (convertPatterns t name pat) ds
       -- rest <- lookInMatches t name pat ms
       if newGuard == g && newDS == ds
         then do
           return (HsAlt s p (HsGuard g) ds)
         else do
           return (HsAlt s (ghead "lookInAlt" newPats) (HsGuard newGuard) newDS)
         
lookInAlt t name pat (alt@(HsAlt s p (HsBody e)  ds)::HsAltP)
   = do
       inscopeNames <- hsVisibleNames e t
       unless (not (name `elem` inscopeNames))
        $ error ("the use of the name: " ++ name ++ " is already in scope!")
       
       let newPats = checkPats name pat [p]
       let convertedPat = convertPat name pat
       newExp <- checkExpr convertedPat e
       newDS <- mapM (convertPatterns t name pat) ds
       -- rest <- lookInMatches t name pat ms
       if newExp == e && newDS == ds
         then do
           return (HsAlt s p (HsBody e) ds)
         else do
           return (HsAlt s (ghead "lookInAlt" newPats) (HsBody newExp) newDS)
 
lookInDo t name pat (inDo@(HsGenerator s p e rest))
   = do
       inscopeNames <- hsVisibleNames e t
       unless (not (name `elem` inscopeNames))
        $ error ("the use of the name: " ++ name ++ " is already in scope!")
       
       let newPats = checkPats name pat [p]
       let convertedPat = convertPat name pat
       newExp <- checkExpr convertedPat e
       newDS <- lookInExps t name pat rest
       -- rest <- lookInMatches t name pat ms
       if newExp == e && newDS == rest
         then do
           return (HsGenerator s p e rest)
         else do
           return (HsGenerator s (ghead "lookInDo" newPats) newExp newDS)
           
lookInList t name pat (inList@(Exp (HsListComp d)))
 = do
      res <- lookInDo t name pat d
      return (Exp (HsListComp res))

lookInExps t name pat (HsLast e) 
   = do
       inscopeNames <- hsVisibleNames e t
       unless (not (name `elem` inscopeNames))
        $ error ("the use of the name: " ++ name ++ " is already in scope!")
       let convertedPat = convertPat name pat
       newExp <- checkExpr convertedPat e
       return (HsLast newExp)

lookInExps t name pat (HsGenerator s p e rest)
   = do
       inscopeNames <- hsVisibleNames e t
       unless (not (name `elem` inscopeNames))
        $ error ("the use of the name: " ++ name ++ " is already in scope!")
       
       let newPats = checkPats name pat [p]
       let convertedPat = convertPat name pat
       newExp <- checkExpr convertedPat e
       newDS <- lookInExps t name pat rest
       -- rest <- lookInMatches t name pat ms
       if newExp == e && newDS == rest
         then do
           return (HsGenerator s p e rest)
         else do
           return (HsGenerator s (ghead "lookInDo" newPats) newExp newDS)

lookInExps t name pat (HsQualifier e rest)
   = do
       inscopeNames <- hsVisibleNames e t
       unless (not (name `elem` inscopeNames))
        $ error ("the use of the name: " ++ name ++ " is already in scope!")
       let convertedPat = convertPat name pat
       newExp <- checkExpr convertedPat e
       newDS <- lookInExps t name pat rest
       return (HsQualifier newExp newDS)
       
lookInExps t name pat (HsLetStmt ds rest)
   = do
       
       let convertedPat = convertPat name pat
       newRest <- lookInExps t name pat rest
       newDS <- mapM (convertPatterns t name pat) ds

       -- rest <- lookInMatches t name pat ms
       if newDS == ds && rest == newRest
         then do
           return (HsLetStmt ds rest)
         else do
           return (HsLetStmt newDS newRest) 
            
checkPats :: String -> HsPatP -> [ HsPatP ] -> [ HsPatP ]
checkPats _ _ [] = []
checkPats name pat (pat2@(Pat (HsPParen p)): ps)
 | pat == pat2  = (Pat (HsPParen (Pat (HsPAsPat (nameToPNT name) p)))) : checkPats name pat ps
 | otherwise =  (Pat (HsPParen res)) : (checkPats name pat ps)
     where
       res = ghead "checkPats HsPParen res" $ checkPats name pat [p]
checkPats name pat (pat2@(Pat (HsPApp i ps)):pss)
 | pat == pat2 = (Pat (HsPAsPat (nameToPNT name) pat2)) : checkPats name pat pss
 | otherwise = (Pat (HsPApp i (checkPats name pat ps))) : checkPats name pat pss
 
checkPats name pat (pat2@(Pat (HsPTuple s ps)):pss)
 | pat == pat2 = (Pat (HsPAsPat (nameToPNT name) pat2)) : checkPats name pat pss
 | otherwise = (Pat (HsPTuple s (checkPats name pat ps))) : checkPats name pat pss
 
checkPats name pat (pat2@(Pat (HsPList s ps)) : pss)
 | pat == pat2 = (Pat (HsPAsPat (nameToPNT name) pat2)) : checkPats name pat pss
 | otherwise   = (Pat (HsPList s (checkPats name pat ps))) : checkPats name pat pss
 
checkPats name pat ((Pat (HsPInfixApp p1 i p2)) : pss)
 = (Pat (HsPInfixApp res1 i res2)) : checkPats name pat pss
     where
       res1 = ghead "checkPats HsPInFixApp res1" $ checkPats name pat [p1]
       res2 = ghead "checkPats HsPInfixApp res2" $ checkPats name pat [p2]
checkPats name pat (p:ps)
 | pat == p  = (Pat (HsPAsPat (nameToPNT name) p)) : checkPats name pat ps
 | otherwise = p : (checkPats name pat ps) 

-- checkGuards [] g = return g
checkGuards _ [] = return []
checkGuards pat@(Pat (HsPAsPat s p)) ((s1, e1, e2):gs)
  = do
       -- rewrite the guard
       newGuard  <- rewriteExp s (rewritePats p) e1 pat
       -- newGuard' <- checkExpr ps newGuard
       
       -- rewrite the RHS of the guard
       rhs       <- rewriteExp s (rewritePats p) e2 pat
       -- rhs'      <- checkExpr ps rhs
       rest <- checkGuards pat gs

       return ((s1, newGuard, rhs):rest)

-- checkExpr :: [ HsPatP ] -> HsExpP -> m HsExpP
-- checkExpr [] e = return e
checkExpr pat@(Pat (HsPAsPat s p)) e
    = do  
        newExp <- rewriteExp s (rewritePats p) e pat  --   error $ show (rewritePats p)
        -- newExp' <- checkExpr ps newExp  
        return newExp
checkExpr _ e = return e

-- rewrite exp checks to see whether the given expression occurs within
-- the second exp. If it does, the expression is replaced with the name of the 'as'
-- pattern.
-- rewriteExp :: String -> HsExpP -> HsExpP -> HsExpP
rewriteExp name e1 e2 t
  = applyTP (full_tdTP (idTP `adhocTP` (inExp e1))) e2
     where
       -- inExp :: HsExpP -> HsExpP -> HsExpP
       inExp (Exp (HsParen e1)::HsExpP) (e2::HsExpP)
        = do
             -- error $ show e2
             allDef <- allDefined e2 t
             if (rmLocs e1) == (rmLocs e2) && (and allDef)
               then do
                  return (nameToExp (pNTtoName name))
               else do
                  return e2             
       inExp (e1::HsExpP) (e2::HsExpP)
         | (rmLocs e1) == (rmLocs e2)  = return (nameToExp (pNTtoName name))
         | otherwise = return e2 
  
allDefined e t
  = applyTU (full_tdTU (constTU [] `adhocTU` inPNT)) e
      where
        inPNT (p@(PNT pname ty _)::PNT)   
         = return [findPN pname t]

rewritePats :: HsPatP -> HsExpP
rewritePats (pat1@(Pat (HsPRec x y)))
  = Exp (HsRecConstr loc0 x (map sortField y))
    where
      sortField :: HsFieldI a HsPatP -> HsFieldI a HsExpP
      sortField (HsField i e) = (HsField i (rewritePats e))

rewritePats (pat1@(Pat (HsPLit x y)))
  = Exp (HsLit x y)

rewritePats (pat1@(Pat (HsPAsPat i p1)))
  = Exp (HsAsPat i (rewritePats p1))

rewritePats (pat1@(Pat (HsPIrrPat p1)))
  = Exp (HsIrrPat (rewritePats p1))

rewritePats (pat1@(Pat (HsPWildCard)))
  = nameToExp "undefined"

rewritePats (pat1@(Pat (HsPApp i p1)))
  = createFuncFromPat i (map rewritePats p1)

rewritePats (pat1@(Pat (HsPList _ p1)))
  = Exp (HsList (map rewritePats p1))

rewritePats (pat1@(Pat (HsPTuple _ p1)))
  = Exp (HsTuple (map rewritePats p1))

rewritePats (pat1@(Pat (HsPInfixApp p1 x p2)))
  =  Exp (HsInfixApp (rewritePats p1)
                     (HsCon x)
                     (rewritePats p2))

rewritePats (pat@(Pat (HsPParen p1)))
  = Exp (HsParen (rewritePats p1))

rewritePats (pat1@(Pat (HsPId (HsVar (PNT (PN (UnQual (i:is)) a) b c)))))
 | isUpper i = (Exp (HsId (HsCon (PNT (PN (UnQual (i:is)) a) b c))))
 | otherwise = (Exp (HsId (HsVar (PNT (PN (UnQual (i:is)) a) b c))))
rewritePats (pat1@(Pat (HsPId (HsCon (PNT (PN (UnQual (i:is)) a) b c)))))
  = (Exp (HsId (HsCon (PNT (PN (UnQual (i:is)) a) b c))))
-- rewritePats p = error $ show p


-- strip removes whitespace and '\n' from a given string
strip :: String -> String
strip [] = []
strip (' ':xs) = strip xs
strip ('\n':xs) = strip xs
strip (x:xs) = x : strip xs

isInfixOf needle haystack = any (isPrefixOf needle) (tails haystack)

--check whether the cursor points to the beginning of the datatype declaration
--taken from RefacADT.hs
checkCursor :: String -> Int -> Int -> HsModuleP -> Either String HsDeclP
checkCursor fileName row col mod
 = case locToTypeDecl of
     Nothing -> Left ("Invalid cursor position. Please place cursor at the beginning of the definition!")
     Just decl -> Right decl
   where
    locToTypeDecl = find (definesPNT (locToPNT fileName (row, col) mod)) (hsModDecls mod)
    
    definesPNT pnt d@(Dec (HsPatBind loc p e ds))
      = findPNT pnt d
    definesPNT pnt d@(Dec (HsFunBind loc ms)) = findPNT pnt d
    definesPNT pnt _ = False

{-|
Takes the position of the highlighted code and returns
the function name, the list of arguments, the expression that has been
highlighted by the user, and any where\/let clauses associated with the
function. 
-}

{-findPattern :: Term t => [PosToken] -- ^ The token stream for the 
                                          -- file to be
                                          -- refactored.
                  -> (Int, Int) -- ^ The beginning position of the highlighting.
                  -> (Int, Int) -- ^ The end position of the highlighting.
                  -> t          -- ^ The abstract syntax tree.
                  -> (SrcLoc, PNT, FunctionPats, HsExpP, WhereDecls) -- ^ A tuple of,
                     -- (the function name, the list of arguments,
                     -- the expression highlighted, any where\/let clauses
                     -- associated with the function).
 -}                    
findPattern toks beginPos endPos t
  = fromMaybe (defaultPNT, defaultPat, error "Invalid pattern selected!")
              (applyTU (once_tdTU (failTU `adhocTU` inMatch 
                                          `adhocTU` inCase
                                          `adhocTU` inDo 
                                          `adhocTU` inList )) t)

    where
       --The selected sub-expression is in the rhs of a match
      inMatch (match@(HsMatch loc1  pnt pats rhs ds)::HsMatchP)
        -- is the highlighted region selecting a pattern?
        | inPat pats == Nothing = Nothing
        | otherwise = do 
                         let pat = fromJust (inPat pats) 
                         Just (pnt, pat, Match match)
      
      inCase (alt@(HsAlt s p rhs ds)::HsAltP)
        | inPat [p] == Nothing = Nothing
        | otherwise = do
                          let pat = fromJust (inPat [p])
                          Just (defaultPNT, pat, MyAlt alt)
                          
      inDo (inDo@(HsGenerator s p e rest)::HsStmtP)
        | inPat [p] == Nothing = Nothing
        | otherwise = do
                          let pat = fromJust (inPat [p])
                          Just (defaultPNT, pat, MyDo inDo)
      inDo x = Nothing
      
      inList (inlist@(Exp (HsListComp (HsGenerator s p e rest)))::HsExpP)
        | inPat [p] == Nothing = Nothing
        | otherwise = do
                          let pat = fromJust (inPat [p])
                          Just (defaultPNT, pat, MyListComp inlist)
      inList x = Nothing
      
      inPat :: [HsPatP] -> Maybe HsPatP
      inPat [] = Nothing
      inPat (p:ps)
       = if p1 /= defaultPat
           then Just p1
           else inPat ps
              where 
                p1 = locToLocalPat beginPos endPos toks p
   --   inPat _ = Nothing
