-----------------------------------------------------------------------------
-- |
-- Module      :  RefacUnfoldAsPatterns
-- Copyright   :  (c) Christopher Brown 2007
--
-- Maintainer  :  cmb21@kent.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- This module contains a transformation for HaRe.
-- unfold all references to an AS pattern in a function.
--
-----------------------------------------------------------------------------

module RefacUnfoldAsPatterns where


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
             
data Expp = MyExp HsExpP | MyStmt (HsStmt HsExpP HsPatP [HsDeclP]) | MyGuard (SrcLoc, HsExpP, HsExpP) | DefaultExp
             deriving (Show)

refacUnfoldAsPatterns args
  = do let 
           fileName    = args!!0
           beginRow         = read (args!!1)::Int
           beginCol         = read (args!!2)::Int
           endRow           = read (args!!3)::Int
           endCol           = read (args!!4)::Int

       AbstractIO.putStrLn "refacUnfoldAsPatterns"

       -- Parse the input file.
       modInfo@(inscps, exps, mod, tokList) <- parseSourceFile fileName
              
       let (pat, term) = findPattern tokList (beginRow, beginCol) (endRow, endCol) mod       
              
       case pat of
         Pat (HsPId (HsVar defaultPNT))
             -> do
                        -- writeRefactoredFiles False [((fileName, m), (newToks, newMod))]
                        -- Allow the highlighting of a particular expression
                        -- rather than a pattern. (For Some).
       
                        let exp = locToExp (beginRow, beginCol) (endRow, endCol) tokList mod
       
                        let (pat, term) = patDefinesExp exp mod
                                                
                        patsInTerm <- getPats term
                        let patsPNT = hsPNTs pat
                        let patsPNT2 = hsPNTs patsInTerm                
                        when (patsPNT `myElem` patsPNT2) $ error "There are conflicts in the binding analysis! Please do a renaming"
                     
                        ((_,m), (newToks, (newMod, _))) <- applyRefac (changeExpression True exp pat) 
                                                                 (Just (inscps, exps, mod, tokList)) fileName
  
                        when (newMod == mod) 
                             $ AbstractIO.putStrLn 
                                      ( "Warning: the expression:\n" ++ ((render.ppi) exp) ++ "\nis not associated with a pattern!" )
        
                        writeRefactoredFiles False [((fileName, m), (newToks, newMod))] 
                        AbstractIO.putStrLn "Completed.\n"
         _ -> do
       
                -- Allow the highlighting of a particular as-pattern
                -- t@p
                -- this should substitute all t for p in scope.
                -- derive the patterns defined in the term (the RHS of the selected pattern)
                patsInTerm <- getPats term
                let patsPNT = hsPNTs pat
                let patsPNT2 = hsPNTs patsInTerm                
                when (patsPNT `myElem` patsPNT2) $ error "There are conflicts in the binding analysis! Please do a renaming"
       
                exp <- getExpAssociatedPat pat mod
                
                let patWOParen = convertPat pat
                            
                ((_,m), (newToks, newMod)) <- doRefac True changeExpression exp patWOParen inscps exps mod tokList fileName
                              
                writeRefactoredFiles False [((fileName, m), (newToks, newMod))]
                AbstractIO.putStrLn "Completed.\n" 
    
myElem :: [PNT] -> [PNT] -> Bool
myElem [] list = False
myElem (p:pnts) list
  | p `elem` list = error ("Please rename: " ++ ((render.ppi) p) ++ " as it conflicts with patterns of the same name.")
  | otherwise     = myElem pnts list
--  = or ((p `elem` list) : [myElem pnts list])


getPats :: (MonadPlus m) => Expp -> m [HsPatP]
getPats (MyExp e)
  = hsPats e
  
getPats (MyStmt (HsGenerator _ p _ rest))
  = do pats <- hsPats p
       result <- getPats (MyStmt rest)
       return (pats ++ result)
getPats (MyStmt (HsQualifier e rest))
  = getPats (MyStmt rest)
getPats (MyStmt (HsLetStmt ds rest))
  = do
       pats <- hsPats ds
       result <- getPats (MyStmt rest)
       return (pats ++ result)
getPats (MyStmt (HsLast e))
 = return []
 
getPats (MyGuard (_, e1, e2))
 = hsPats e2    -- modify this? lets in e2? 
getPats _ = error "Pattern is not associated with an as-pattern. Check Pattern is highlight correctly!"

hsPats :: (MonadPlus m, Term t) => t -> m [HsPatP]
hsPats t = applyTU (full_tdTU (constTU [] `adhocTU` inPat)) t
           where
             inPat (p::HsPatP) = return [p]
                
convertPat :: HsPatP -> HsPatP
convertPat (Pat (HsPParen p)) = p
convertPat p = p

doRefac predPat f [] p inscps exps mod tokList fileName = 
  return ((fileName, True), (tokList, mod))       
doRefac predPat f (exp:_) p inscps exps mod tokList fileName
 = do
      ((_,m), (newToks, (newMod, newPat))) <- applyRefac (f predPat exp p) (Just (inscps, exps, mod, tokList)) fileName
      
      writeRefactoredFiles True [((fileName, m), (newToks, newMod))]
      
      modInfo@(inscps', exps', mod', tokList') <- parseSourceFile fileName
      
      newExps <- getExpAssociatedPat p mod'
            
      -- error $ show newExps
      
      if length newExps == 1
        then do
           rest <- doRefac False f newExps newPat inscps' exps' mod' tokList' fileName 
      
           return rest           
        else do
           let (_, es) = splitAt 1 newExps
      
           rest <- doRefac False f es newPat inscps' exps' mod' tokList' fileName 
      
           return rest
       
getExpAssociatedPat :: (Term t, MonadPlus m) => HsPatP -> t -> m [HsExpP]
getExpAssociatedPat (Pat (HsPParen p)) t = getExpAssociatedPat p t
getExpAssociatedPat pat@(Pat (HsPAsPat p1 p)) t
 = applyTU (full_tdTU (constTU [] `adhocTU` inPnt)) t
    where
       inPnt e@(Exp (HsId (HsVar p2))) 
         | definesPNT p1 p2 = return [e]
       inPnt _ = return []
         

-- changeExpression [] pat (a,b,t) = return t      
changeExpression predPat exp pat (a, b,t)
  = do 
        names <- addName exp t
        (newExp, newPat) <- checkPats names pat exp
        newT  <- update exp newExp t
        -- liftIO (AbstractIO.putStrLn $ show (exp,newExp))
        
        if predPat == True
          then do
            newT2 <- update pat newPat newT                
            return (newT2, newPat)
          else do
            return (newT, newPat)
       
addName e mod   = do
                   names <- hsVisibleNames e mod 
                   return names


                   
checkPats :: (MonadPlus m, Monad m) => [String] -> HsPatP -> HsExpP -> m (HsExpP, HsPatP)
checkPats names (Pat (HsPParen p)) e 
      = do
           (a,b) <- checkPats names p e
           return (a, Pat (HsPParen b))
           
checkPats names (pat@(Pat (HsPAsPat i p))) e
      = do
          -- names <- addName e t
          let (newExp1, newPat) = rewritePats names 1 p
          newExp2 <- rewriteExp i newExp1 e
          return ((Exp (HsParen newExp2)), (Pat (HsPAsPat i newPat)))


-- rewrite exp checks to see whether the given expression occurs within
-- the second exp. If it does, the expression is replaced with the name of the 'as'
-- pattern.
-- rewriteExp :: String -> HsExpP -> HsExpP -> HsExpP
rewriteExp name e1 e2
  = applyTP (full_tdTP (idTP `adhocTP` (inExp e1))) e2
     where
       -- inExp :: HsExpP -> HsExpP -> HsExpP
       inExp (Exp (HsParen e1)::HsExpP) (e2@(Exp (HsId (HsVar pnt@(PNT pname ty loc))))::HsExpP)
        = do
             
             if (rmLocs pnt) == (rmLocs name) 
              then do
               return e1
              else do 
                return e2 
                    
       inExp (e1::HsExpP) (e2@(Exp (HsId (HsVar pnt@(PNT pname ty loc))))::HsExpP)
         | findPNT pnt pname  = return e1
         | otherwise = return e2
         
       inExp e1 e2 = return e2
  
allDefined e t
  = applyTU (full_tdTU (constTU [] `adhocTU` inPNT)) e
      where
        inPNT (p@(PNT pname ty _)::PNT)   
         = return [findPN pname t]

rewritePats :: [ String ] -> Int  -> HsPatP -> (HsExpP, HsPatP)
rewritePats names index (pat1@(Pat (HsPRec x y)))
  = (Exp (HsRecConstr loc0 x (map sortField y)), pat1)
    where
      sortField :: HsFieldI a HsPatP -> HsFieldI a HsExpP
      sortField (HsField i e) = (HsField i es)
                                  where
                                   (es, ps) = rewritePats names index e
       
rewritePats _ _ (pat1@(Pat (HsPLit x y)))
  = (Exp (HsLit x y), pat1)

rewritePats names index (pat1@(Pat (HsPAsPat i p1)))
  = (Exp (HsAsPat i es), (Pat (HsPAsPat i ps)))
      where
       (es, ps) = rewritePats names index p1

rewritePats names index (pat1@(Pat (HsPIrrPat p1)))
  = (Exp (HsIrrPat es), Pat (HsPIrrPat ps))
      where
       (es, ps) = rewritePats names index p1
       
rewritePats names i (pat1@(Pat (HsPWildCard)))
  = (nameToExp (mkNewName "a" names i), nameToPat (mkNewName "a" names i))

rewritePats names i (pat1@(Pat (HsPApp i1 p1)))
  = (createFuncFromPat i1 es, Pat (HsPApp i1 ps))
     where
       es = map fst result
       ps = map snd result
       result = myMap (rewritePats names) i p1

rewritePats names i (pat1@(Pat (HsPList i2 p1)))
  = (Exp (HsList es), Pat (HsPList i2 ps))
     where
       es = map fst result
       ps = map snd result
       result = myMap (rewritePats names) i p1
       
rewritePats names i (pat1@(Pat (HsPTuple i1 p1)))
  = (Exp (HsTuple es), Pat (HsPTuple i1 ps))
       where
        es = map fst result
        ps = map snd result
        result = myMap (rewritePats names) i p1
  

rewritePats names i (pat1@(Pat (HsPInfixApp p1 x p2)))
  =  (Exp (HsInfixApp es
                      (HsCon x)
                      es2),
      Pat (HsPInfixApp ps
                       x
                       ps2))
                     
     where
       (es, ps) = rewritePats names i p1
       (es2, ps2) = rewritePats names (i+42) p2

rewritePats names i (pat@(Pat (HsPParen p1)))
  = (Exp (HsParen es), (Pat (HsPParen ps)))
       where
        (es, ps) = rewritePats names i p1

rewritePats _ _ (pat1@(Pat (HsPId (HsVar (PNT (PN (UnQual (i:is)) a) b c)))))
 | isUpper i = ((Exp (HsId (HsCon (PNT (PN (UnQual (i:is)) a) b c)))), pat1)
 | otherwise = ((Exp (HsId (HsVar (PNT (PN (UnQual (i:is)) a) b c)))), pat1)
rewritePats _ _ (pat1@(Pat (HsPId (HsCon (PNT (PN (UnQual (i:is)) a) b c)))))
  = ((Exp (HsId (HsCon (PNT (PN (UnQual (i:is)) a) b c)))), pat1)
-- rewritePats p = error $ show p

myMap _ _ [] = []
myMap f i (x:xs) = f i x : myMap f (i+1) xs

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

findGuard [] exp = error "The expression is not defined within a guard!"
findGuard ((a ,e1, e2):gs) exp
  | findEntityWithLocation exp e2 = (a,e1,e2)
  | otherwise         = findGuard gs exp

patDefinesExp exp t
  = fromMaybe (defaultPat, DefaultExp)
              (applyTU (once_tdTU (failTU `adhocTU` inMatch 
                                          `adhocTU` inCase
                                          `adhocTU` inDo 
                                          `adhocTU` inList )) t)
      where
       --The selected sub-expression is in the rhs of a match
       inMatch (match@(HsMatch loc1  pnt pats (HsGuard (g@(_,_,e):gs)) ds)::HsMatchP)
         -- is the highlighted region selecting a pattern?
         | inPat pats == Nothing = Nothing
         | otherwise = do 
                         let guard = findGuard (g:gs) exp
                         let pat = fromJust (inPat pats) 
                         Just (pat, MyGuard guard)

       
       inMatch (match@(HsMatch loc1  pnt pats (HsBody rhs) ds)::HsMatchP)
        -- is the highlighted region selecting a pattern?
        | inPat pats == Nothing = Nothing
        | otherwise = do 
                         let pat = fromJust (inPat pats) 
                         Just (pat, MyExp rhs)
      
       inCase (alt@(HsAlt s p (HsGuard (g@(_,_,e):gs)) ds)::HsAltP)
        | inPat [p] == Nothing = Nothing
        | otherwise = do
                          let guard = findGuard (g:gs) exp
                          let pat = fromJust (inPat [p])
                          Just (pat, MyGuard guard)

      
       inCase (alt@(HsAlt s p (HsBody rhs) ds)::HsAltP)
        | inPat [p] == Nothing = Nothing
        | otherwise = do
                          let pat = fromJust (inPat [p])
                          Just (pat, MyExp rhs)
                          
       inDo (inDo@(HsGenerator s p e rest)::HsStmtP)
        | inPat [p] == Nothing = Nothing
        | otherwise = do
                          let pat = fromJust (inPat [p])
                          Just (pat, MyStmt rest)
       inDo x = Nothing
      
       inList (inlist@(Exp (HsListComp (HsGenerator s p e rest)))::HsExpP)
        | inPat [p] == Nothing = Nothing
        | otherwise = do
                          let pat = fromJust (inPat [p])
                          Just (pat, MyStmt rest)
       inList x = Nothing
      
      
       inPat p 
         = (applyTU (once_tdTU (failTU `adhocTU` worker))) p
      
       worker (pat@(Pat (HsPAsPat i p))::HsPatP)
         | expToPNT exp == i
                         = Just pat
       worker p = Nothing
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
  = fromMaybe (defaultPat, DefaultExp)
              (applyTU (once_tdTU (failTU `adhocTU` inMatch 
                                          `adhocTU` inCase
                                          `adhocTU` inDo 
                                          `adhocTU` inList )) t)

    where
       --The selected sub-expression is in the rhs of a match
      inMatch (match@(HsMatch loc1  pnt pats (HsGuard (g@(_,_,e):gs)) ds)::HsMatchP)
        -- is the highlighted region selecting a pattern?
        | inPat pats == Nothing = Nothing
        | otherwise = do 
                         let pat = fromJust (inPat pats) 
                         Just (pat, MyGuard g)

       
      inMatch (match@(HsMatch loc1  pnt pats (HsBody rhs) ds)::HsMatchP)
        -- is the highlighted region selecting a pattern?
        | inPat pats == Nothing = Nothing
        | otherwise = do 
                         let pat = fromJust (inPat pats) 
                         Just (pat, MyExp rhs)
      
      inCase (alt@(HsAlt s p (HsGuard (g@(_,_,e):gs)) ds)::HsAltP)
        | inPat [p] == Nothing = Nothing
        | otherwise = do
                          let pat = fromJust (inPat [p])
                          Just (pat, MyGuard g)

      
      inCase (alt@(HsAlt s p (HsBody rhs) ds)::HsAltP)
        | inPat [p] == Nothing = Nothing
        | otherwise = do
                          let pat = fromJust (inPat [p])
                          Just (pat, MyExp rhs)
                          
      inDo (inDo@(HsGenerator s p e rest)::HsStmtP)
        | inPat [p] == Nothing = Nothing
        | otherwise = do
                          let pat = fromJust (inPat [p])
                          Just (pat, MyStmt rest)
      inDo x = Nothing
      
      inList (inlist@(Exp (HsListComp (HsGenerator s p e rest)))::HsExpP)
        | inPat [p] == Nothing = Nothing
        | otherwise = do
                          let pat = fromJust (inPat [p])
                          Just (pat, MyStmt rest)
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

