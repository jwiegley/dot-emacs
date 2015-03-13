module RefacGenFold where

import PFE0
import HsTokens
-- ++AZ++ import TypeCheck
import PrettyPrint
import PosSyntax
import HsName
import HsLexerPass1
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
--  import System
import System.IO
import Relations
import Ents
import Data.Set (toList)
import Data.List
import System.IO.Unsafe
import System.Cmd
-- import LocalSettings
import RefacSimplify
import StateMT(WithState,withSt,withStS,getSt,setSt,updSt,updSt_)
import qualified Control.Exception as CE (catch)
import EditorCommands
-- | An argument list for a function which of course is a list of paterns.
type FunctionPats = [HsPatP]

-- | A list of declarations used to represent a where or let clause.
type WhereDecls = [HsDeclP]

data PatFun = Mat | Patt | Er deriving (Eq, Show)

genFold args
 = do
     let fileName = ghead "fileName'" args
         beginRow         = read (args!!1)::Int
         beginCol         = read (args!!2)::Int
         endRow           = read (args!!3)::Int
         endCol           = read (args!!4)::Int
     AbstractIO.putStrLn "genFold"

     modName <-fileNameToModName fileName
     let modName1 = convertModName modName
     (inscps, exps, mod, tokList)<-parseSourceFile fileName
     let subExp = locToExp (beginRow, beginCol) (endRow, endCol) tokList mod
     let (ty, pnt, pats, wh)
             = findDefNameAndExp tokList
                                 (beginRow, beginCol)
                                 (endRow, endCol)
                                 mod

     ((_,m), (newToks, (newMod, e))) <- applyRefac (addCommentDec pnt) (Just (inscps, exps, mod, tokList)) fileName



     writeRefactoredFiles False [((fileName, m), (newToks, newMod))]

     (inscps', exps', mod', tokList') <- parseSourceFile fileName


     ((_,m'), (newToks', (newMod',parsed))) <- applyRefac (retrieveDecAndRemove pnt e)
                                                           (Just (inscps', exps', mod', tokList')) fileName

     let pnt' = declToPNT parsed
     -- undo the added entry!
     undoLatestInHistory
     (inscps2, exps2, mod2, tokList2)<-parseSourceFile fileName
     ((_,m'''), (newToks''', newMod''')) <- applyRefac (changeExpression pnt pnt' parsed subExp)
                                                        (Just (inscps2, exps2, mod2, tokList2)) fileName
     writeRefactoredFiles False  [((fileName, m'''), (newToks''', newMod'''))]



     AbstractIO.putStrLn "Completed.\n"

addCommentDec pnt (_,_,t)
 = do
      tks <- extractComment (pNTtoPN pnt) t
      let tksString = concatMap getName tks
      let commentDef = dropWhile (==' ') (parseComment (reverse tksString))
      if '=' `elem` commentDef
       then do
         mod <- insertTerm (dropWhile (==' ') (reverse commentDef)) (pNTtoPN pnt) t
         return (mod, (dropWhile (==' ') (reverse commentDef)))
       else do
         error "Please define an equation within a comment above the definition under scrutiny."

retrieveDecAndRemove pnt e (_,_,t)
 = do
      let parsedDec = retrieveDec pnt e t
      -- mod <- removeDec e t
      return (t, parsedDec)

retrieveDec pnt exp t
  = fromMaybe (error ("Previous record of definition not found! " ++ exp))
              (applyTU (once_tdTU (failTU `adhocTU` inDec)) t)
      where


        inDec d@(Dec (HsPatBind _ _ _ _))
          | (render.ppi) d == exp
              = Just d
        inDec d@(Dec (HsFunBind l matches))
          | rendered matches exp
               = do
                  let x = rendered2 matches exp
                  Just (Dec (HsFunBind l [x]))
        inDec d = Nothing

        rendered [] _ = False
        rendered (m:ms) e
          | rmLine ( rmToks ((render.ppi) m)) == rmLine ( rmToks e ) = True
          | otherwise           = rendered ms e

        rendered2 [] _ = error "Error in rendered2"
        rendered2 (m:ms) e
          | rmLine ( rmToks ((render.ppi) m)) == rmLine ( rmToks e ) = m
          | otherwise           = rendered2 ms e

        rmToks x = (rmRBracket.rmLBracket.rmLine.rmSpace) x

        rmSpace x = filter (/=' ') x
        rmLine x = filter (/='\n') x
        rmLBracket x = filter (/='(') x
        rmRBracket x = filter (/=')') x
removeDec exp t
  = applyTP (stop_tdTP (idTP `adhocTP` inDec)) t
      where
        inDec (d::HsDeclP)
          | (render.ppi) d == exp
              = do
                   rmDecl (declToPName2 d) True [d]
                   return d
        inDec d = return d




parseComment :: String -> String
parseComment [] = []
parseComment ('}':('-':xs)) = parseComment' xs
parseComment (x:xs) = parseComment xs

parseComment' :: String -> String
parseComment' [] = []
parseComment' ('-':('{':xs)) = ""
parseComment' (x:xs) = x : (parseComment' xs)

getName :: PosToken -> String
getName (_, ((Pos _ _ _), s)) = s

changeExpression pnt pntComment d exp (_,_,t)
 = do
      mod <- changeExpression' pnt pntComment d exp t
      return mod

changeExpression' pnt pntComment d exp t
  = applyTP (stop_tdTP (failTP `adhocTP` (inExp d exp))) t
      where
        inExp (Dec (HsPatBind _ p (HsBody e2) ds)) exp (e::HsExpP)
          | sameOccurrence exp e
              = do
                  if rmAllLocs e2 == rmAllLocs e
                    then do
                      res <- update e (nameToExp (pNTtoName (patToPNT p))) e
                      return res
                    else do
                      mzero
        inExp (dec@(Dec (HsFunBind s matches))::HsDeclP) exp (e::HsExpP)
          | sameOccurrence exp e
                = do
                      let match@(HsMatch loc name pats (HsBody e2) ds) = getMatch pntComment matches
                      let newExp = searchForRHS pnt exp t
                      let (pred, newParams) = rewriteExp pats newExp e2
                      if pred
                         then do
                          -- let patsConverd = map (render.ppi) newPats
                          res <- update e (createFunc pntComment (map patToExp newParams)) e
                          return res
                         else do
                          mzero
        inExp d exp e = mzero

rewriteExp :: [HsPatP] -> HsExpP -> HsExpP -> (Bool, [HsPatP])
rewriteExp pats (Exp (HsParen e)) e2 = rewriteExp pats e e2
rewriteExp pats e (Exp (HsParen e2)) = rewriteExp pats e e2
rewriteExp pats (Exp (HsLit s x)) (Exp (HsLit s1 x2))
 | x == x2 = (True, pats)
rewriteExp pats (Exp (HsId (HsCon x))) (Exp (HsId (HsCon y)))
 | x == y = (True, pats)
rewriteExp pats n m@(Exp (HsId (HsVar i2)))
 | checkPNTInPat pats i2 = (True, getPatFromPats pats n i2)
rewriteExp pats n@(Exp (HsId (HsVar i1))) (Exp (HsId (HsVar i2)))
 | (pNTtoName i1) /= (pNTtoName i2) && checkPNTInPat pats i2 = (True, getPatFromPats pats n i2)
 | (pNTtoName i1) == (pNTtoName i2)  = (True, pats)
 | isLocalPNT i1 && isLocalPNT i2 = (True, pats)
 | otherwise = (False, pats)
rewriteExp pats a@(Exp (HsApp e1 e2)) b@(Exp (HsApp e3 e4))
 | pred1 == True && pred2 == True = (True, pats2)
   where
    (pred1, pats1) = rewriteExp pats  e1 e3
    (pred2, pats2) = rewriteExp pats1 e2 e4
rewriteExp pats a@(Exp (HsInfixApp e1 o1 e2)) b@(Exp (HsInfixApp e3 o2 e4))
 | o1 == o2 && (pred1 && pred2) = (True, pats2)
     where
       (pred1, pats1) = rewriteExp pats e1 e3
       (pred2, pats2) = rewriteExp pats1 e2 e4
rewriteExp pats a@(Exp (HsTuple e1)) b@(Exp (HsTuple e2))
 | length e1 == length e2 && pred = (True, pats2)
 | otherwise = (False, pats)
    where
      (pred, pats2) = checkList pats e1 e2
rewriteExp pats a@(Exp (HsList e1)) b@(Exp (HsList e2))
 | length e1 == length e2 = (True, pats2)
 | otherwise = (False, pats)
    where
      (pred, pats2) = checkList pats e1 e2
rewriteExp pats a@(Exp (HsLeftSection e1 i1)) b@(Exp (HsLeftSection e2 i2))
 | i1 == i2 && pred1 = (True, pats1)
     where
       (pred1, pats1) = rewriteExp pats e1 e2
rewriteExp pats a@(Exp (HsRightSection i1 e1)) b@(Exp (HsRightSection i2 e2))
 | i1 == i2 && pred1 = (True, pats1)
     where
       (pred1, pats1) = rewriteExp pats e1 e2
rewriteExp pats a@(Exp (HsEnumFrom e1)) b@(Exp (HsEnumFrom e2))
 | pred1 = (True, pats1)
   where
     (pred1, pats1) = rewriteExp pats e1 e2
rewriteExp pats a@(Exp (HsEnumFromTo e1 e2)) b@(Exp (HsEnumFromTo e3 e4))
 | pred1 && pred2 = (True, pats2)
    where
       (pred1, pats1) = rewriteExp pats e1 e3
       (pred2, pats2) = rewriteExp pats1 e2 e4
rewriteExp pats a@(Exp (HsEnumFromThen e1 e2)) b2@(Exp (HsEnumFromThen e3 e4))
 | pred1 && pred2 = (True, pats2)
    where
       (pred1, pats1) = rewriteExp pats e1 e3
       (pred2, pats2) = rewriteExp pats1 e2 e4
rewriteExp pats a@(Exp (HsEnumFromThenTo e1 e2 e3)) b@(Exp (HsEnumFromThenTo e4 e5 e6))
 | pred1 && pred2 && pred3 = (True, pats3)
    where
      (pred1, pats1) = rewriteExp pats e1 e4
      (pred2, pats2) = rewriteExp pats1 e2 e5
      (pred3, pats3) = rewriteExp pats2 e3 e6
rewriteExp pats a@(Exp (HsIf e1 e2 e3)) b@(Exp (HsIf e4 e5 e6))
 | pred1 && pred2 && pred3 = (True, pats3)
    where
      (pred1, pats1) = rewriteExp pats e1 e4
      (pred2, pats2) = rewriteExp pats1 e2 e5
      (pred3, pats3) = rewriteExp pats2 e3 e6
rewriteExp pats a@(Exp (HsNegApp s e)) b@(Exp (HsNegApp s2 e2))
 | pred = (True, pats1)
   where
     (pred, pats1) = rewriteExp pats e e2
rewriteExp pats a@(Exp (HsListComp stmts1)) b@(Exp (HsListComp stmts2))
 | pred = (True, pats1)
   where
     (pred, pats1) = rewriteExpStmts pats stmts1 stmts2
rewriteExp pats (Exp (HsDo stmts1)) (Exp (HsDo stmts2))
 | pred = (True, pats1)
    where
      (pred, pats1) = rewriteExpStmts pats stmts1 stmts2
rewriteExp pats a@(Exp (HsLambda ps e1)) b@(Exp (HsLambda ps2 e2))
 | wildCardAllPNs ps == wildCardAllPNs ps2 && pred = (True, pats1)
   where
     (pred, pats1) = rewriteExp pats e1 (localRewriteExp e2 (localRewritePats ps ps2))
     localRewritePats [] ps = []
     localRewritePats ps [] = []
     localRewritePats (p1:p1s) (p2:p2s)
        = (rewritePat p2 p1) : (localRewritePats p1s p2s)

     localRewriteExp e [] = e
     localRewriteExp e (p1:p1s)
       = let e1' = rewritePatsInExp p1 e  in localRewriteExp e1' p1s

rewriteExp pats a@(Exp (HsRecConstr s i fields1)) b@(Exp (HsRecConstr s2 i2 fields2))
 | i == i2 && pred = (True, pats1)
    where
      (pred, pats1) = rewriteExpFields pats fields1 fields2
rewriteExp pats a@(Exp (HsRecUpdate s1 e1 fields1)) b@(Exp (HsRecUpdate s2 e2 fields2))
 | pred1 && pred2 = (True, pats2)
   where
     (pred1, pats1) = rewriteExp pats e1 e2
     (pred2, pats2) = rewriteExpFields pats1 fields1 fields2
rewriteExp pats a@(Exp (HsCase e1 alts1)) b@(Exp (HsCase e2 alts2))
  | pred1 && pred2 = (True, pats2)
    where
      (pred1, pats1) = rewriteExp pats e1 e2
      (pred2, pats2) = rewriteExpAlts pats1 alts1 alts2

-- rewriteExp pats e1 e2 = error $ ">" ++ (show (pats, e1, e2))
rewriteExp pats e1 e2 = (False, pats) --  error $ ">" ++ (show (pats, e1, e2))

rewriteExpFields pats [] _ = (True, pats)
rewriteExpFields pats _ [] = (True, pats)
rewriteExpFields pats ((HsField i1 e1):f1) ((HsField i2 e2):f2)
  | pred && (i1 == i2 && pred2) = (True, pats2)
  | otherwise = (False, pats)
     where
       (pred, pats1) = rewriteExp pats e1 e2
       (pred2, pats2) = rewriteExpFields pats1 f1 f2

rewriteExpAlts pats [] _ = (True, pats)
rewriteExpAlts pats _ [] = (True, pats)
rewriteExpAlts pats ((HsAlt _ p1 (HsBody e1) ds1):alts1) ((HsAlt _ p2 (HsBody e2) ds2):alts2)
  | pred && (wildCardAllPNs p1 == wildCardAllPNs p2 && pred2) = (True, pats2)
  | otherwise = (False, pats)
     where
       (pred, pats1) = rewriteExp pats e1 (rewritePatsInExp (rewritePat p2 p1) e2)
       (pred2, pats2) = rewriteExpAlts pats1 alts1 alts2
rewriteExpAlts pats ((HsAlt _ p1 (HsGuard gs1) ds1):alts1) ((HsAlt _ p2 (HsGuard gs2) ds2):alts2)
  | (wildCardAllPNs p1 == wildCardAllPNs p2 && pred2) = (True, pats2)
  | otherwise = (False, pats)
     where
       -- (pred, pats1) = rewriteExp pats e1 e2
       (pred2, pats2) = rewriteExpGuards pats gs1 res
       res =  (rewritePatsInGuard (rewritePat p2 p1) gs2)
rewriteExpAlts pats _ _ = (False, pats)

rewriteExpGuards pats [] _ = (True, pats)
rewriteExpGuards pats _ [] = (True, pats)
rewriteExpGuards pats ((_ ,e1,e2):gs1) ((_, e3, e4):gs2)
  | pred1 && pred2 && pred3 = (True, pats3)
    where
     (pred1, pats1) = rewriteExp pats e1 e3
     (pred2, pats2) = rewriteExp pats1 e2 e4
     (pred3, pats3) = rewriteExpGuards pats2 gs1 gs2


rewriteExpStmts pats s1@(HsGenerator _ p1 e1 m1) s2@(HsGenerator _ p2 e2 m2)
 | wildCardAllPNs p1 == wildCardAllPNs p2 && pred1 && pred2 = (True, pats2)
  where
   (pred1, pats1) =  rewriteExp pats e1 e2
   (pred2, pats2) = rewriteExpStmts pats1 m1 m2
rewriteExpStmts pats (HsLast e1) (HsLast e2)
 | wildCardAllPNs e1 == wildCardAllPNs e2 = (True, pats)
 -- = error $ show $ rewriteExp pats e1 e2
rewriteExpStmts pats (HsQualifier e1 stmts) (HsQualifier e2 stmts2)
 | pred1 && pred2 = (True, pats2)
  where
   (pred1, pats1) =  rewriteExp pats e1 e2
   (pred2, pats2) = rewriteExpStmts pats1 stmts stmts2
rewriteExpStmts pats (HsLetStmt ds1 stmts) (HsLetStmt ds2 stmts2)
 = rewriteExpStmts pats stmts stmts2
rewriteExpStmts pats s1 s2 = (False, pats)

changeAllNames :: PNT -> PNT -> PNT
changeAllNames pnt  t =runIdentity (applyTP (full_buTP (idTP `adhocTP` l)) t)
   where
         l ((PN (UnQual n) s))
           | n /= (pNTtoName pnt) =  return ((PN (UnQual (pNTtoName pnt)) s))
           | otherwise = return ((PN (UnQual n) s))

rewritePat :: HsPatP -> HsPatP -> HsPatP
rewritePat a@(Pat (HsPId (HsVar x))) b@(Pat (HsPId (HsVar y)))
  = (Pat (HsPId (HsVar (changeAllNames y x))))
rewritePat a@(Pat (HsPId (HsCon x))) b@(Pat (HsPId (HsCon y)))
  = a
rewritePat a@(Pat (HsPLit _ _)) b@(Pat (HsPLit _ _))
  = a
rewritePat a@(Pat (HsPNeg _ _)) b@(Pat (HsPNeg _ _))
  = a
rewritePat a@(Pat (HsPSucc _ _ _)) b@(Pat (HsPSucc _ _ _))
  = a
rewritePat a@(Pat (HsPInfixApp p1 i p2)) b@(Pat (HsPInfixApp p3 i2 p4))
  = (Pat (HsPInfixApp (rewritePat p1 p3) i (rewritePat p2 p4)))
rewritePat a@(Pat (HsPApp i ps)) b@(Pat (HsPApp i2 ps2))
  = (Pat (HsPApp i (rewritePat' ps ps2)))
rewritePat a@(Pat (HsPTuple s ps)) b@(Pat (HsPTuple s2 ps2))
  = (Pat (HsPTuple s (rewritePat' ps ps2)))
rewritePat a@(Pat (HsPList s ps)) b@(Pat (HsPList s2 ps2))
  = (Pat (HsPList s (rewritePat' ps ps2)))
rewritePat a@(Pat (HsPParen p1)) b@(Pat (HsPParen p2))
  = (Pat (HsPParen (rewritePat p1 p2)))
rewritePat a@(Pat (HsPAsPat i p1)) b@(Pat (HsPAsPat i2 p2))
  = (Pat (HsPAsPat i (rewritePat p1 p2)))
rewritePat a@(Pat (HsPWildCard)) b@(Pat (HsPWildCard))
 = a
rewritePat a@(Pat (HsPIrrPat p1)) b@(Pat (HsPIrrPat p2))
 = Pat (HsPIrrPat (rewritePat p1 p2))
rewritePat a b = a

rewritePat' :: [HsPatP] -> [HsPatP] -> [HsPatP]
rewritePat' [] _ = []
rewritePat' x [] = x
rewritePat' (x:xs) (y:ys)
  = rewritePat x y : rewritePat' xs ys


rewritePatsInExp :: HsPatP -> HsExpP -> HsExpP
rewritePatsInExp p a@(Exp (HsId (HsVar x)))
 | isTopLevelPNT x = a
 | otherwise
   = (Exp (HsId (HsVar newPNT)))
     where
       newPNT = grabPNT x (hsPNTs p)
rewritePatsInExp p (Exp (HsInfixApp e1 o e2))
  = (Exp (HsInfixApp e1' o e2'))
      where
        e1' = rewritePatsInExp p e1
        e2' = rewritePatsInExp p e2
rewritePatsInExp p (Exp (HsApp e1 e2))
  = (Exp (HsApp e1' e2'))
      where
        e1' = rewritePatsInExp p e1
        e2' = rewritePatsInExp p e2
rewritePatsInExp p (Exp (HsNegApp s e))
  = (Exp (HsNegApp s e'))
     where
       e' = rewritePatsInExp p e
rewritePatsInExp p (Exp (HsLambda ps e))
  = (Exp (HsLambda ps e'))
     where
       e' = rewritePatsInExp p e
rewritePatsInExp p (Exp (HsLet ds e))
  = (Exp (HsLet ds e'))
     where
       e' = rewritePatsInExp p e
rewritePatsInExp p (Exp (HsIf e1 e2 e3))
  = (Exp (HsIf e1' e2' e3'))
     where
       e1'  = rewritePatsInExp p e1
       e2'  = rewritePatsInExp p e2
       e3'  = rewritePatsInExp p e3
rewritePatsInExp p (Exp (HsCase e alts))
  = (Exp (HsCase e' alts'))
      where
        e' = rewritePatsInExp p e
        alts' = rewritePatsInAlts p alts
rewritePatsInExp p (Exp (HsDo stmts))
  = (Exp (HsDo stmts'))
     where
       stmts' = rewritePatsInStmts p stmts
rewritePatsInExp p (Exp (HsTuple es))
  = (Exp (HsTuple es'))
     where
      es' = map (rewritePatsInExp p) es
rewritePatsInExp p (Exp (HsList es))
  = (Exp (HsList es'))
     where
       es' = map (rewritePatsInExp p) es
rewritePatsInExp p (Exp (HsParen e))
  = (Exp (HsParen (rewritePatsInExp p e)))
rewritePatsInExp p (Exp (HsLeftSection e (HsVar x)))
  = (Exp (HsLeftSection e' (HsVar newPNT)))
     where
       e' = rewritePatsInExp p e'
       newPNT = grabPNT x (hsPNTs p)
rewritePatsInExp p (Exp (HsRightSection (HsVar x) e))
  = (Exp (HsRightSection (HsVar newPNT) e'))
     where
       e' = rewritePatsInExp p e'
       newPNT = grabPNT x (hsPNTs p)
rewritePatsInExp p (Exp (HsRecConstr s i fields))
  = (Exp (HsRecConstr s newPNT fields'))
      where
        newPNT = grabPNT i (hsPNTs p)
        fields' = rewritePatsInFields p fields
rewritePatsInExp p (Exp (HsRecUpdate s e fields))
  = (Exp (HsRecUpdate s e' fields'))
      where
       e' = rewritePatsInExp p e
       fields' = rewritePatsInFields p fields
rewritePatsInExp p (Exp (HsEnumFrom e))
 = (Exp (HsEnumFrom e'))
    where
     e' = rewritePatsInExp p e
rewritePatsInExp p (Exp (HsEnumFromTo e1 e2))
 = (Exp (HsEnumFromTo e1' e2'))
    where
      e1' = rewritePatsInExp p e1
      e2' = rewritePatsInExp p e2
rewritePatsInExp p (Exp (HsEnumFromThen e1 e2))
 = (Exp (HsEnumFromThen e1' e2'))
     where
       e1' = rewritePatsInExp p e1
       e2' = rewritePatsInExp p e2
rewritePatsInExp p (Exp (HsEnumFromThenTo e1 e2 e3))
 = (Exp (HsEnumFromThenTo e1' e2' e3'))
     where
       e1' = rewritePatsInExp p e1
       e2' = rewritePatsInExp p e2
       e3' = rewritePatsInExp p e3
rewritePatsInExp p (Exp (HsListComp stmts))
 = (Exp (HsListComp stmts'))
     where
       stmts' = rewritePatsInStmts p stmts
rewritePatsInExp p e = e

rewritePatsInStmts :: HsPatP -> HsStmtP -> HsStmtP
rewritePatsInStmts p (HsGenerator s p2 e stmts)
 = (HsGenerator s p2 e' stmts')
   where
     e' = rewritePatsInExp p e
     stmts' = rewritePatsInStmts p stmts
rewritePatsInStmts p (HsQualifier e stmts)
 = (HsQualifier e' stmts')
    where
     e' = rewritePatsInExp p e
     stmts' = rewritePatsInStmts p stmts
rewritePatsInStmts p (HsLetStmt ds stmts)
 = (HsLetStmt ds stmts')
    where
     stmts' = rewritePatsInStmts p stmts
rewritePatsInStmts p (HsLast e)
 = (HsLast e')
    where
      e' = rewritePatsInExp p e

rewritePatsInFields :: HsPatP -> [HsFieldP] -> [HsFieldP]
rewritePatsInFields p [] = []
rewritePatsInFields p ((HsField i e):fs)
 = (HsField newPNT e') : (rewritePatsInFields p fs)
    where
      newPNT = grabPNT i (hsPNTs e)
      e' = rewritePatsInExp p e

rewritePatsInAlts :: HsPatP -> [HsAltP] -> [HsAltP]
rewritePatsInAlts p [] = []
rewritePatsInAlts p ((HsAlt s p2 (HsBody e) ds):alts)
 = (HsAlt s p2 (HsBody e') ds) : (rewritePatsInAlts p alts)
     where
       e' = rewritePatsInExp p e
rewritePatsInAlts p ((HsAlt s p2 (HsGuard gs) ds):alts)
 = (HsAlt s p2 (HsGuard gs') ds) : (rewritePatsInAlts p alts)
     where
       gs' = rewritePatsInGuard p gs

rewritePatsInGuard :: HsPatP -> [(SrcLoc, HsExpP, HsExpP)] -> [(SrcLoc, HsExpP, HsExpP)]
rewritePatsInGuard p [] = []
rewritePatsInGuard p ((s, e1, e2):gs)
 = (s, e1', e2') : (rewritePatsInGuard p gs)
    where
      e1' = rewritePatsInExp p e1
      e2' = rewritePatsInExp p e2


grabPNT :: PNT -> [PNT] -> PNT
grabPNT x [] = x
grabPNT x (y:ys)
  | defineLoc x == defineLoc y = y
  | otherwise = grabPNT x ys


checkList :: [HsPatP] -> [HsExpP] -> [HsExpP] -> (Bool, [HsPatP])
checkList pats [] [] = (True, pats)
checkList pats [e] [l] = rewriteExp pats e l
checkList pats (e:es) (l:ls)
        | pred = checkList pats' es ls
        | otherwise = (False, pats')
           where
             (pred, pats') = rewriteExp pats e l
checkPNTInPat :: [HsPatP] -> PNT -> Bool
checkPNTInPat [] _ = False
checkPNTInPat (p:ps) i
        | defineLoc i == (SrcLoc "__unknown__" 0 0 0) = False
        | defineLoc i == defineLoc (patToPNT p) = True
        | otherwise = checkPNTInPat ps i


getPatFromPats :: [HsPatP] -> HsExpP -> PNT -> [HsPatP]
getPatFromPats [] _ _ = []
getPatFromPats (p:pats) e i2
     | defineLoc i2 == (SrcLoc "__unknown__" 0 0 0) = p : (getPatFromPats pats e i2)
     | defineLoc i2 == defineLoc (patToPNT p) = (expToPat e) ++ (getPatFromPats pats e i2)
     | otherwise = p : (getPatFromPats pats e i2)

patToExp :: HsPatP -> HsExpP
patToExp (Pat (HsPId x)) = (Exp (HsId x))
patToExp (Pat (HsPLit s l)) = (Exp (HsLit s l))
patToExp (Pat (HsPInfixApp p1 i p2)) = (Exp (HsInfixApp (patToExp p1) (HsCon i) (patToExp p2)))
patToExp (Pat (HsPApp pnt p2)) = (Exp (HsApp (nameToExp (pNTtoName pnt)) (cApp p2)))
                                    where
                                      cApp :: [HsPatP] -> HsExpP
                                      cApp [p] = patToExp p
                                      cApp (p:ps) = Exp (HsApp (cApp (init (p:ps))) (patToExp (last ps)))
patToExp (Pat (HsPTuple s ps)) = (Exp (HsTuple (map patToExp ps)))
patToExp (Pat (HsPList s ps)) = (Exp (HsList (map patToExp ps)))
patToExp (Pat (HsPParen p1)) = (Exp (HsParen (patToExp p1)))
patToExp (Pat (HsPAsPat pnt pat)) = (Exp (HsId (HsVar pnt)))
patToExp (Pat (HsPIrrPat p)) = patToExp p
patToExp (Pat (HsPWildCard)) = nameToExp "undefined"

expToPat :: HsExpP -> [HsPatP]
expToPat (Exp (HsId x)) = [Pat (HsPId x)]
expToPat (Exp (HsLit s l)) = [Pat (HsPLit s l)]
expToPat (Exp (HsInfixApp e1 (HsVar i) e2)) = [Pat (HsPInfixApp (ghead "expToPat" $ expToPat e1)
                                                             i (ghead "expToPat" $ expToPat e2))]
expToPat (Exp (HsInfixApp e1 (HsCon i) e2)) = [Pat (HsPInfixApp (ghead "expToPat" $ expToPat e1)
                                                             i (ghead "expToPat" $ expToPat e2))]
expToPat e@(Exp (HsApp e1 e2)) =    [Pat (HsPApp (nameToPNT " ")
                                                   (concatMap expToPat exps))]
                               where
                                 exps = flatternApp e
expToPat (Exp (HsLambda ps e)) = ps
expToPat (Exp (HsTuple es)) = concatMap expToPat es   --[Pat (HsPTuple loc0 (concatMap expToPat es))]
expToPat (Exp (HsList es)) = concatMap expToPat es
expToPat (Exp (HsParen e1)) = [Pat (HsPParen (ghead "expToPat" $ expToPat e1))]
expToPat e = []

flatternApp :: HsExpP -> [HsExpP]
flatternApp (Exp (HsApp e1 e2)) = flatternApp e1 ++ flatternApp e2
flatternApp (Exp (HsParen e)) = flatternApp e
flatternApp x = [x]

searchForRHS pnt exp t
  = (fromMaybe (error "Could not find the right hand side for the commented definition!"))
    (applyTU (once_tdTU (failTU `adhocTU` (inDec exp))) t)
      where
        inDec e (pat@(Dec (HsPatBind loc1 ps rhs@(HsBody e2) ds))::HsDeclP)
         | findEntity e e2
            = do
               let newExp = symbolicallyTie exp e2 []
               Just newExp

        inDec e (dec@(Dec (HsFunBind s matches))::HsDeclP)
         | findPNT pnt matches
          = do
               let match@(HsMatch loc name pats rhs ds) = getMatch pnt matches

               if findEntity e (extractRHS e rhs)
                  then do
                         let newExp = symbolicallyTie exp (extractRHS e rhs) pats
                         Just newExp
                  else do
                         mzero
        inDec _ d = mzero

findGuard e [] = error "Cannot find highlight expression!"
findGuard e ((_,_,x):xs)
  | findEntity e x = x
  | otherwise = findGuard e xs
extractRHS e (HsBody x) = x
extractRHS e (HsGuard gs) = findGuard e gs

symbolicallyTie exp (Exp (HsParen e)) pats = symbolicallyTie exp e pats
symbolicallyTie exp n@(Exp (HsCase e alts)) pats
     = symbolicallyTie' alts  -- (Exp (HsCase e [symbolicallyTie' alts]))
        where
          symbolicallyTie' [] = error "Error in symbolic evaluation: expression does not occur on the RHS!"
          symbolicallyTie' (a@(HsAlt l p (HsGuard gs) ds):as)
           | findEntity exp gs
            = zipPatExp e n a' pats
           | findEntity exp ds           -- selected definition is in where clause of a case alt.
            = zipPatExp e n a' pats
            where
              a' = (HsAlt l p (HsBody exp) ds)
          symbolicallyTie' (a@(HsAlt l p (HsBody e2) ds):as)
           | findEntity exp e2
               = zipPatExp e n a' pats
           | findEntity exp ds           -- selected definition is in where clause of a case alt.
               = zipPatExp e n a' pats
           | otherwise = symbolicallyTie' as
            where
              a' = (HsAlt l p (HsBody exp) ds)
symbolicallyTie exp e pats = exp
-- utility functions
getMatch :: PNT -> [HsMatchP] -> HsMatchP
getMatch _ [] = error "Please select a case in top-level expression scope!"
getMatch pnt (match@(HsMatch loc name pats rhs ds):ms)
  | useLoc pnt == useLoc name      = match
  | otherwise        = getMatch pnt ms

convertModName (PlainModule s) = s
convertModName m@(MainModule f) = modNameToStr m

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
                  -> (PatFun, PNT, FunctionPats, WhereDecls) -- ^ A tuple of,
                     -- (the function name, the list of arguments,
                     -- the expression highlighted, any where\/let clauses
                     -- associated with the function).

findDefNameAndExp toks beginPos endPos t
  = fromMaybe (Er, defaultPNT, [], [])
              (applyTU (once_buTU (failTU `adhocTU` inMatch `adhocTU` inPat)) t)

    where
      --The selected sub-expression is in the rhs of a match
      inMatch (match@(HsMatch loc1  pnt pats rhs@(HsBody e) ds)::HsMatchP)
        | locToExp beginPos endPos toks rhs /= defaultExp
          = Just (Mat, pnt, pats, ds)
      inMatch (match@(HsMatch loc1  pnt pats rhs@(HsGuard e) ds)::HsMatchP)
        | locToExp beginPos endPos toks rhs /= defaultExp
          = Just (Mat, pnt, pats, ds)
      inMatch _ = Nothing


      --The selected sub-expression is in the rhs of a pattern-binding
      inPat (pat@(Dec (HsPatBind loc1 ps rhs ds))::HsDeclP)
        | locToExp beginPos endPos toks rhs /= defaultExp
            = if isSimplePatBind pat
                 then Just (Patt, patToPNT ps, [], ds)
                 else Just (Patt, pnt, pats, ds)
                    where
                      (_, pnt, pats, ds') = findDefining pat t
                      findDefining pats t
                        = fromMaybe (error "Error: the selected entity is a top level complex pattern binding!")
                                    (applyTU (once_buTU (failTU `adhocTU` inMatch')) t)

                      inMatch' (match@(HsMatch loc1  pnt pats rhs@(HsBody e) ds)::HsMatchP)
                         | pat `elem` ds = Just (Mat, pnt, pats, ds)
                         | findEntity pat e = Just (Mat, pnt, pats, ds)
                      inMatch' (match@(HsMatch loc1  pnt pats rhs@(HsGuard e) ds)::HsMatchP)
                         | pat `elem` ds = Just (Mat, pnt, pats, ds)
                         | findEntity pat e = Just (Mat, pnt, pats, ds)
                      inMatch' _ = Nothing

      inPat _ = Nothing
