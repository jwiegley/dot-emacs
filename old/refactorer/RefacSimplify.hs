module RefacSimplify (zipPatExp, simplifyExpr) where

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
import System.IO.Unsafe
import System.Cmd
import LocalSettings(evaluate,evaluate_result)
import Control.Monad.CatchIO
-- import qualified Evaluate as Evaluate

-- | An argument list for a function which of course is a list of paterns.
type FunctionPats = [HsPatP]

-- | A list of declarations used to represent a where or let clause.
type WhereDecls = [HsDeclP]

data PatFun = Mat | Patt | Er deriving (Eq, Show)

simplifyExpr args
 =do let fileName = ghead "fileName'" args
         beginRow         = read (args!!1)::Int
         beginCol         = read (args!!2)::Int
         endRow           = read (args!!3)::Int
         endCol           = read (args!!4)::Int
     AbstractIO.putStrLn "SimplifyExpr"

     modName <-fileNameToModName fileName
     let modName1 = convertModName modName
     AbstractIO.putStrLn $ show modName1
     (inscps, exps, mod, tokList)<-parseSourceFile fileName
     let subExp = locToExp (beginRow, beginCol) (endRow, endCol) tokList mod
     let (ty, pnt, pats, _, wh)
             = findDefNameAndExp tokList
                                 (beginRow, beginCol)
                                 (endRow, endCol)
                                 mod

     case subExp of
       (Exp (HsCase _ _))
         -> do

               ((_,m), (newToks, newMod)) <- applyRefac
                                                       (addExpression pnt subExp)
                                                       (Just (inscps, exps, mod, tokList)) fileName
               writeRefactoredFiles True [((fileName, m), (newToks, newMod))]

               -- need to reparse to capture added definition...
               (inscps2, exps2, mod2, tokList2)<-parseSourceFile fileName
               ((_,m'), (newToks', newMod')) <- applyRefac
                                                          (changeExpression fileName (modNameToStr modName) pnt subExp)
                                                          (Just (inscps2, exps2, mod2, tokList2)) fileName
               writeRefactoredFiles True [((fileName, m'), (newToks', newMod'))]
               -- can we evaluate the result to get a further simplification?
               -- Warning: this may cause the refactorer to loop indefinately,
               -- and will only succedd in decidable evaluations that can be
               -- converted to string via show.
               {-(inscps3, exps3, mod3, tokList3)<-parseSourceFile fileName
               ((_,m''), (newToks'', newMod'')) <- applyRefac
                                                          (evalExpression fileName ses (modNameToStr modName) pnt subExp)
                                                          (Just (inscps3, exps3, mod3, tokList3)) fileName
               writeRefactoredFiles True [((fileName, m''), (newToks'', newMod''))] -}



               AbstractIO.putStrLn "Completed.\n"
       x -> error "Please highlight a case expression!"
convertModName (PlainModule s) = s
convertModName m@(MainModule f) = modNameToStr m

evalExpression f ses modName pnt e (_,_,t)
 = do
      mod <- evalExpression' f ses modName pnt e t
      return mod

evalExpression' f ses modName pnt e t
  = applyTP (full_tdTP (idTP `adhocTP` inDec)) t
     where
       inDec (dec@(Dec (HsFunBind s matches))::HsDeclP)
         | findPNT pnt matches
             = do
                  let match@(HsMatch loc name pats rhs@(HsBody exp) ds) = getMatch pnt matches
                  (free,decs) <- hsFreeAndDeclaredNames match
                  let lambdas  = getFreeLambdas rhs

                  -- lift $ AbstractIO.putStrLn $ show lambdas

                  let newPats   = map createCall (pats++lambdas)
                      newName   = pNTtoName name
                  result <- ghcEvalExpr f ((newName ++ " " ++ (concatMapWithSpace (render.ppi) newPats))) modName
                  -- result <- liftIO $ ghcEvalExpr f ((newName ++ " " ++ (concatMapWithSpace (render.ppi) newPats))) modName
                  case result of
                    "-1" -> return dec
                    _ -> do
                            let newExp = (Exp (HsId (HsVar (nameToPNT result))))

                                 -- insertComment ("Result of " ++ newName ++" :" ++ result) (pNTtoPN (patToPNT p)) t

                            update exp newExp exp
                            return dec

       inDec (dec@(Dec (HsPatBind s p rhs@(HsBody exp) ds)))
         | findPNT pnt p
            = do
                  -- let match@(HsMatch loc name pats rhs ds) = getMatch pnt matches

                  -- try and evaluate the highlighted expression
                  -- first let's transform the case so that each pattern match returns
                  -- a number, we can then use this to determine which
                  -- clause has suceeded.
                  (free,decs) <- hsFreeAndDeclaredNames dec

                  let lambdas  = getFreeLambdas rhs
                      lambdas2 = getAllLambdas rhs


                  let newPats   = map createCall lambdas
                      newName   = pNTtoName (patToPNT p)
                  result <- ghcEvalExpr f ((newName ++ " " ++ (concatMapWithSpace (render.ppi) newPats))) modName
                  case result of
                    ("-1") -> do
                                 return dec
                    _ -> do
                                 let newExp = (Exp (HsId (HsVar (nameToPNT result))))

                                 -- insertComment ("Result of " ++ newName ++" :" ++ result) (pNTtoPN (patToPNT p)) t

                                 update exp newExp exp
                                 return dec
       inDec x = return x
changeExpression f modName pnt e (_,_,t)
 = do
      mod <- changeExpression' f modName pnt e t
      return mod

changeExpression' f modName pnt e t
  = applyTP (full_tdTP (idTP `adhocTP` inDec)) t
     where
       inDec (dec@(Dec (HsFunBind s matches))::HsDeclP)
         | findPNT pnt matches
             = do
                  let match@(HsMatch loc name pats rhs ds) = getMatch pnt matches

                  -- try and evaluate the highlighted expression
                  -- first let's transform the case so that each pattern match returns
                  -- a number, we can then use this to determine which
                  -- clause has suceeded.
                  (free,decs) <- hsFreeAndDeclaredNames match

                  let lambdas  = getFreeLambdas rhs

                  -- lift $ AbstractIO.putStrLn $ show lambdas

                  let newPats   = map createCall (pats++lambdas)
                      newName   = mkNewName (pNTtoName name) (free++decs) 0
                  result <- ghcEvalExpr f ((newName ++ " " ++ (concatMapWithSpace (render.ppi) newPats))) modName
                  case result of
                    ("-1") -> do
                               -- remove the temp declaration...
                               let declsP = map declToPName2 (hsDecls t)
                                   declP = findDec newName declsP
                               rmDecl declP False (hsDecls t)
                               return dec
                    _    -> do
                               let ps = patternise (hsDecls rhs)
                               -- lift $ AbstractIO.putStrLn $ show (ps)
                               lift $ AbstractIO.putStrLn $ (result \\ result)

                               newExp <- rewriteExp result (pats++(ps++lambdas)) e rhs

                               -- remove the temp declaration...
                               let declsP = map declToPName2 (hsDecls t)
                                   declP = findDec newName declsP


                               rmDecl declP False (hsDecls t)
                               return dec

       inDec (dec@(Dec (HsPatBind s p rhs ds)))
         | findPNT pnt p
            = do
                  -- let match@(HsMatch loc name pats rhs ds) = getMatch pnt matches

                  -- try and evaluate the highlighted expression
                  -- first let's transform the case so that each pattern match returns
                  -- a number, we can then use this to determine which
                  -- clause has suceeded.
                  (free,decs) <- hsFreeAndDeclaredNames dec

                  let lambdas  = getFreeLambdas rhs
                      lambdas2 = getAllLambdas rhs
                  -- lift $ AbstractIO.putStrLn $ show lambdas

                  let newPats   = map createCall lambdas
                      newName   = mkNewName (pNTtoName (patToPNT p)) (free++decs) 0
                  result <- ghcEvalExpr f ((newName ++ " " ++ (concatMapWithSpace (render.ppi) newPats))) modName
                  case result of
                    ("-1") -> do
                               -- remove the temp declaration...
                               let declsP = map declToPName2 (hsDecls t)
                                   declP = findDec newName declsP
                               rmDecl declP False (hsDecls t)
                               return dec
                    _ -> do
                            let ps = patternise (hsDecls rhs)
                            lift $ AbstractIO.putStrLn $ (result \\ result)

                            newExp <- rewriteExp result ([p]++(ps++lambdas2)) e rhs


                            -- remove the temp declaration...
                            let declsP = map declToPName2 (hsDecls t)
                                declP = findDec newName declsP

                            -- lift $ AbstractIO.putStrLn $ show (declP, (hsDecls t))


                            rmDecl declP False (hsDecls t)
                            return dec

       inDec x = return x

       patternise :: [HsDeclP] -> [HsPatP]
       patternise
        = (nub.ghead "patternise").applyTU (full_tdTU (constTU [] `adhocTU` inPat))


       inPat (Dec (HsPatBind _ (Pat (HsPId (HsVar x))) (HsBody e) ds))
         = return [Pat (HsPAsPat x (ghead "inPat" $ expToPat e))]

       inPat (Dec (HsPatBind _ (Pat (HsPTuple l ps)) (HsBody e) ds))
         = do
              let res = expToPat e
              return (swapPositions ps res)

       inPat (Dec (HsPatBind _ (Pat (HsPList l ps)) (HsBody e) ds))
         = do
              let res = expToPat e
              return (swapPositions ps res)

       inPat (Dec (HsPatBind _ p (HsBody e) ds))
         = return [p]

       swapPositions :: [HsPatP] -> [HsPatP] -> [HsPatP]
       swapPositions [] x = x
       swapPositions x [] = x
       swapPositions (x:xs) (y:ys)
         = (changeDefineLoc (defineLoc (patToPNT x)) y) : (swapPositions xs ys)


       changeDefineLoc::(Term t)=>SrcLoc -> t -> t
       changeDefineLoc s e = runIdentity (applyTP (full_tdTP (idTP `adhocTP` (inLoc s))) e)

       inLoc s (SrcLoc f c row col)
         = return s
       -- inLoc s loc = return loc

       defLocs e = ((nub.ghead "toRelativeLoc").applyTU (full_tdTU (constTU []
                                                              `adhocTU` inPnt ))) e

       inPnt pnt@(PNT pn ty loc)
            |defineLoc pnt == useLoc pnt= return [(\(SrcLoc _ _ r c)->(r,c)) (srcLoc pn)]
       inPnt _ = return []




       -- inPat d = []

       -- traverse into the expression
       -- two cases to consider:
       -- something of the form
       -- 1:   x = (a,b)
       --       then return x@(a,b)
       -- 2:   (x,y) = (a,b)
       --        then return (a,b) (replacing a and b location with x and y).
       -- expToPatCall :: HsPatP -> HsExpP -> [HsPatP]
       -- expToPatCall (Pat (HsPId x)) e = (Pat (HsPAsPat x (expToPat e)))





       expToPat :: HsExpP -> [HsPatP]
       expToPat (Exp (HsId x)) = [Pat (HsPId x)]
       expToPat (Exp (HsLit s l)) = [Pat (HsPLit s l)]
       expToPat (Exp (HsInfixApp e1 (HsCon i) e2)) = [Pat (HsPInfixApp (ghead "expToPat" $ expToPat e1)
                                                             i (ghead "expToPat" $ expToPat e2))]
       expToPat (Exp (HsApp e1 e2)) = [Pat (HsPApp (expToPNT e1)
                                                   (expToPat e2))]
       -- expToPat (Exp (HsNegApp s e)) = [Pat (HsPNeg s e)]
       expToPat (Exp (HsLambda ps e)) = ps
       expToPat (Exp (HsTuple es)) = concatMap expToPat es   --[Pat (HsPTuple loc0 (concatMap expToPat es))]
       expToPat (Exp (HsList es)) = concatMap expToPat es
       expToPat (Exp (HsParen e1)) = [Pat (HsPParen (ghead "expToPat" $ expToPat e1))]
       expToPat _ = []


       findDec :: String -> [PName] -> PName
       findDec n [] = defaultPN
       findDec n (p:ps)
        | n == (pNtoName p) = p
        | otherwise         = findDec n ps

       rewriteExp result pats e t
          = applyTP (stop_tdTP (failTP `adhocTP` (subExp result pats))) t
       subExp r pats exp@((Exp _)::HsExpP)
          | sameOccurrence exp e
               = do
                    newExp <- rewriteExp2 r pats exp
                    -- error $ show (exp, e, newExp)
                    update exp newExp exp
          | otherwise
                  = mzero

       rewriteExp2 r pats n@(Exp (HsCase e alts))
         = do
             -- there are basically two cases to consider.
             -- the first is that the patterns in the case scrutiny
             -- are bound in the LHS. This is the easy case.
             -- the more difficult case is when the patterns are
             -- bound else where, or a combination of the two.
             -- It is neccessary to check if patterns are bound
             -- in lets/lambdas etc and convert to pattern if
             -- possible.

             -- ergo, pats is the predetermined set of pats.
             -- these are calculated at the call site for rewriteExp.

             -- e may be an explicit variable that is bound
             -- in the pattern bindings. If it is, then
             -- let's get the pattern and rename variables, if
             -- needed.

             let pat = getPatBind pats e
                 zippedPat = zipPatExp e n (alts !! (read r::Int)) pats
             -- lift $ AbstractIO.putStrLn $ show zippedPat
             return zippedPat

zipPatExp e (Exp (HsCase e' alts)) a@(HsAlt _ p (HsGuard e2) ds) pats = (Exp (HsCase e' [a]))
zipPatExp e n (HsAlt _ p (HsBody e2) ds) pats
      = res
        where
         res = altToExp (flatternPat p) (zipPatExp'' (zipPatExp' e p) pats) e2
         zipPatExp' :: HsExpP -> HsPatP -> [(HsExpP, HsPatP)]
         zipPatExp' e@(Exp (HsTuple xs)) (Pat (HsPTuple _ ys))
           = zip xs ys
         zipPatExp' e@(Exp (HsList xs)) (Pat (HsPList _ ys))
           = zip xs ys
         zipPatExp' e p = [(e,p)]

         zipPatExp'' :: [(HsExpP, HsPatP)] -> [HsPatP] -> [(HsExpP, HsPatP)]
         zipPatExp'' [] _ = []
         zipPatExp'' ((x,y):xs) pats
          | res == [] = ( x,y) : (zipPatExp'' xs pats)
          | otherwise = (patToExp (ghead "zipPatExp''" res), y) : (zipPatExp'' xs pats)
            where
             res = getPatBind pats x

flatternPat :: HsPatP -> [HsPatP]
flatternPat (Pat (HsPAsPat i p)) = flatternPat p
flatternPat (Pat (HsPApp i p)) = p
flatternPat (Pat (HsPTuple _ p)) = p
flatternPat (Pat (HsPList _ p)) = p
flatternPat (Pat (HsPInfixApp p1 i p2)) = (flatternPat p1) ++ (flatternPat p2)
flatternPat (Pat (HsPParen p)) = flatternPat p
-- flatternPat pnt (Pat (HsPId i)) = 1
flatternPat p = [p]


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
-- expToPat (Exp (HsLambda ps e)) = ps
expToPat (Exp (HsTuple es)) = [Pat (HsPTuple loc0 (concatMap expToPat es))]
expToPat (Exp (HsList es)) = [Pat (HsPList loc0 (concatMap expToPat es))]
expToPat (Exp (HsParen e1))
 | expToPat e1 /= [] = [Pat (HsPParen (ghead "expToPat" $ expToPat e1))]
expToPat e = []

patToExp :: HsPatP -> HsExpP
patToExp (Pat (HsPId x)) = (Exp (HsId x))
patToExp (Pat (HsPLit s l)) = (Exp (HsLit s l))
patToExp (Pat (HsPInfixApp p1 i p2)) = (Exp (HsInfixApp (patToExp p1) (HsCon i) (patToExp p2)))
patToExp (Pat (HsPApp pnt p2)) = (cApp ((nameToPat (pNTtoName pnt)) : p2))
                                    where
                                      cApp :: [HsPatP] -> HsExpP
                                      cApp [p] = patToExp p
                                      cApp (p:ps) = Exp (HsApp (cApp (init (p:ps))) (patToExp (last ps)))
patToExp (Pat (HsPTuple s ps)) = (Exp (HsTuple (map patToExp ps)))
patToExp (Pat (HsPList s ps)) = (Exp (HsList (map patToExp ps)))
patToExp (Pat (HsPParen p1)) = (Exp (HsParen (patToExp p1)))
patToExp p@(Pat (HsPAsPat pnt pat)) = patToExp pat
patToExp (Pat (HsPIrrPat p)) = patToExp p
patToExp (Pat (HsPWildCard)) = nameToExp "undefined"

flatternApp :: HsExpP -> [HsExpP]
flatternApp (Exp (HsApp e1 e2)) = flatternApp e1 ++ flatternApp e2
flatternApp (Exp (HsParen e)) = flatternApp e
flatternApp x = [x]


altToExp :: [HsPatP] -> [(HsExpP, HsPatP)] -> HsExpP -> HsExpP
altToExp p [] e = e
altToExp p pats e
          = symbolicTrans p pats e -- (myMap fromAsPat pats) e
             where
              myMap f [] = []
              myMap f ((x,y):xs)
                = (f x, y): (myMap f xs)
              fromAsPat :: HsPatP -> HsPatP
              fromAsPat (Pat (HsPAsPat _ p)) = p
              fromAsPat p = p

symbolicTrans :: [HsPatP] -> [(HsExpP, HsPatP)] -> HsExpP -> HsExpP
symbolicTrans p [] e = e
symbolicTrans p pats e
          = rewritePatsInExp p pats e

rewriteExpPat ((p1,p2):pats) (Exp (HsId (HsVar i)))
   | findPNT i (patToPNT p2) = (Exp (HsId (HsVar (patToPNT p1))))
rewriteExpPat p q = q
       -- rewriteExpPat p q = error $ show (p,q)

unravelAndFind :: [HsPatP] -> PNT -> HsExpP -> HsPatP -> HsExpP
unravelAndFind _ i p@(Exp (HsLit x y)) q
 = (Exp (HsLit x y))
unravelAndFind ps i p@(Exp (HsId (HsVar i2))) q@(Pat (HsPId (HsVar i3)))
  | (pNTtoName i2) `elem` (map pNTtoName (hsPNTs q))   = (Exp (HsId (HsVar i)))
  | q `elem` ps = (Exp (HsId (HsVar i2))) -- not a top level entity
  | otherwise = (Exp (HsId (HsVar i)))
unravelAndFind ps i p@(Exp (HsId (HsVar i2))) q
  | (rmAllLocs i2) `elem` (map rmAllLocs (hsPNTs q))   = (Exp (HsId (HsVar i)))
  | q `elem` ps = (Exp (HsId (HsVar i2))) -- not a top level entity
  | otherwise = (Exp (HsId (HsVar i)))
unravelAndFind _ i (Exp (HsInfixApp e1 _ e2)) (Pat (HsPInfixApp p3 _ p4))
  | defineLoc i == defineLoc (patToPNT p3) = (Exp (HsId (HsVar (expToPNT e1))))
  | defineLoc i == defineLoc (patToPNT p4) = (Exp (HsId (HsVar (expToPNT e2))))
unravelAndFind ps i e@(Exp (HsApp e1 e2)) p@(Pat (HsPApp pnt pats2))
 = unravelAndFind2 i (flatternApp e) ((nameToPat (pNTtoName pnt)) : pats2)

 -- = (Exp (HsApp (unravelAndFind ps i e1 p)
 --               (unravelAndFind ps i e2 p)))
--   = unravelAndFind2 i (flatternApp e) pats2
unravelAndFind _ i p1@(Exp (HsTuple exps)) p2@(Pat (HsPTuple _ pats2))
        = unravelAndFind2 i exps pats2
       -- unravelAndFind i p1@(Pat (HsPTuple _ pats)) p2
       -- = unravelAndFind2
unravelAndFind ps x (Exp (HsParen p)) y = unravelAndFind ps x p y
unravelAndFind ps x y (Pat (HsPParen p)) = unravelAndFind ps x y p
unravelAndFind _ _ p q@(Pat (HsPId x)) = p
unravelAndFind _ i p q = (Exp (HsId (HsVar i)))



unravelAndFind2 :: PNT -> [HsExpP] -> [HsPatP] -> HsExpP
unravelAndFind2 i [] _ = Exp (HsId (HsVar i))
unravelAndFind2 i _ [] = Exp (HsId (HsVar i))
unravelAndFind2 i (p:ps) (p2:ps2)
         | defineLoc (patToPNT p2) == defineLoc i = Exp (HsId (HsVar (expToPNT p)))
         | otherwise = unravelAndFind2 i ps ps2

myMap _ [] _ = False
myMap f ((p,q):pats) i
         = or ((f (hsPNTs q) i) : [myMap f pats i])

definedInPats [] e = False
definedInPats pats i
        = myMap checkPNTInPat pats i


getPatFromPats _ [] i = Exp (HsId (HsVar i))
getPatFromPats ps ((p,q):pats) i
     | myMap checkPNTInPat ((p,q):pats) i = checkPQ ps ((p,q):pats)
     | otherwise = getPatFromPats ps pats i
            where
              checkPQ ps [] = Exp (HsId (HsVar i))
              checkPQ ps ((p,q):pats)
                | checkPNTInPat (hsPNTs q) i = unravelAndFind ps i p q
                | otherwise = checkPQ ps pats


rewritePatsInExp :: [HsPatP] -> [(HsExpP, HsPatP)] -> HsExpP -> HsExpP
rewritePatsInExp _ pats e@(Exp (HsLit s i)) = e
rewritePatsInExp p pats e@(Exp (HsId (HsVar i)))
         | definedInPats pats i =  getPatFromPats p pats i
         | otherwise = e
rewritePatsInExp _ pats e@(Exp (HsId (HsCon i)))  = e

rewritePatsInExp p pats (Exp (HsInfixApp e1 i e2))
         = (Exp (HsInfixApp (rewritePatsInExp p pats e1) i (rewritePatsInExp p pats e2)))

rewritePatsInExp p pats e@(Exp (HsApp e1 e2))
         = (Exp (HsApp (rewritePatsInExp p pats e1) (rewritePatsInExp p pats e2)))

rewritePatsInExp p pats (Exp (HsNegApp s e))
         = Exp (HsNegApp s (rewritePatsInExp p pats e))

rewritePatsInExp p pats l@(Exp (HsLambda ps e))
         = Exp (HsLambda ps (rewritePatsInExp p pats e))

rewritePatsInExp p pats (Exp (HsLet ds e))
         = Exp (HsLet ds (rewritePatsInExp p pats e))

rewritePatsInExp p pats (Exp (HsIf e1 e2 e3))
         = Exp (HsIf e1' e2' e3')
            where
              e1' = rewritePatsInExp p pats e1
              e2' = rewritePatsInExp p pats e2
              e3' = rewritePatsInExp p pats e3
rewritePatsInExp p pats (Exp (HsCase e alts)) -- test this!!
         = Exp (HsCase (rewritePatsInExp p pats e) (rewritePatsInAlts p pats alts))

rewritePatsInExp p pats (Exp (HsTuple es))
         = Exp (HsTuple (map (rewritePatsInExp p pats) es))
rewritePatsInExp p pats (Exp (HsList es))
         = Exp (HsList (map (rewritePatsInExp p pats) es))
rewritePatsInExp p pats (Exp (HsParen e))
         = Exp (HsParen (rewritePatsInExp p pats e))
rewritePatsInExp p pats (Exp (HsRecConstr s i fields))
         = Exp (HsRecConstr s i (rewritePatsInFields p pats fields))
rewritePatsInExp p pats (Exp (HsRecUpdate s e1 fields))
         = Exp (HsRecUpdate s (rewritePatsInExp p pats e1) (rewritePatsInFields p pats fields))
rewritePatsInExp _ pats e = e
       -- check whether any of the PNTs are defined in the Pat or not...

rewritePatsInFields p pats [HsField i e] = [HsField i (rewritePatsInExp p pats e)]
rewritePatsInFields p pats ((HsField i e):fs)
  = (HsField i (rewritePatsInExp p pats e)) : (rewritePatsInFields p pats fs)

rewritePatsInAlts p pats [HsAlt s p2 (HsBody e) ds] = [HsAlt s p2 (HsBody (rewritePatsInExp p pats e)) ds]
rewritePatsInAlts p pats ((HsAlt s p2 (HsBody e) ds):fs)
  = (HsAlt s p2 (HsBody (rewritePatsInExp p pats e)) ds) : (rewritePatsInAlts p pats fs)


checkPNTInPat :: [PNT] -> PNT -> Bool
checkPNTInPat [] _ = False
checkPNTInPat (p:ps) i
        | defineLoc i == (SrcLoc "__unknown__" 0 0 0) = False
        | defineLoc i == defineLoc p = True
        | otherwise = checkPNTInPat ps i


getPatBind :: [HsPatP] -> HsExpP -> [HsPatP]
getPatBind pats (Exp (HsParen e)) = getPatBind pats e
getPatBind [] e = []
getPatBind (p:ps) e@(Exp (HsLit x y))
           = [Pat (HsPLit x y)]
getPatBind (p:ps) e@(Exp (HsId (HsVar i)))
         | definesPNT i (patToPNT p) = [p]
        -- | checkPNTInPat (hsPNTs p) i = [p]
         | otherwise = getPatBind ps e
getPatBind pats e@(Exp (HsTuple es))
         = concatMap (getPatBind pats) es
getPatBind pats e@(Exp (HsList es))
         = concatMap (getPatBind pats) es
getPatBind pats (Exp (HsApp e1 e2)) = []
getPatBind pats (Exp (HsInfixApp e1 o1 e2)) = []
-- getPatBind x y = error $ show (x,y)
getPatBind x y = [] -- error $ show (x,y)

getAllLambdas :: Term t => t -> [HsPatP]
getAllLambdas
  = (nub.concat).applyTU (full_tdTU (constTU [] `adhocTU` inExp3))
      where
       inExp3 (Exp (HsLambda ps e)) = return ps
       inExp3 e1 = return []
getFreeLambdas :: Term t => t -> [HsPatP]
getFreeLambdas
  = (fromMaybe []).applyTU (once_tdTU (failTU `adhocTU` inExp))
      where
       inExp (Exp (HsApp (Exp (HsParen (Exp (HsLambda _ _)))) _)) = Just []
       inExp (Exp (HsLambda ps e))
            = do let res = getFreeLambdas e
                 Just (ps++res)
       inExp _ = Nothing


createCall (Pat (HsPList  s pats)) = (Pat (HsPList s (map createCall pats)))
createCall p@(Pat (HsPLit _ _)) = p
createCall (Pat (HsPAsPat _ p))
  = createCall p
createCall (Pat (HsPInfixApp p1 i p2)) = (Pat (HsPInfixApp (createCall p1) i (createCall p2)))
createCall (Pat (HsPParen p)) = (Pat (HsPParen (createCall p)))
createCall (Pat (HsPId (HsVar i))) = (Pat (HsPId (HsVar (nameToPNT "undefined"))))
createCall p@(Pat (HsPId (HsCon i))) = p
createCall (Pat (HsPApp i pats)) = (Pat (HsPApp i (map createCall pats)))
createCall (Pat (HsPTuple s ps)) = (Pat (HsPTuple s (map createCall ps)))
createCall p = error ("createCall: " ++ (show p))

createFun name names pats newExp ds
  = (Dec (HsFunBind loc0 [HsMatch loc0 (nameToPNT newName) pats (HsBody newExp) ds]), newName)
     where
       newName = mkNewName (pNTtoName name) names 0

       rewriteCase (Exp (HsCase e alts))
        = (Exp (HsCase e (rewriteAlts 0 alts)))
       rewriteCase e = e

       rewriteAlts i [] = []
       rewriteAlts i ((HsAlt s p (HsBody e) ds):as)
        -- = (HsAlt s p (HsBody (Exp (HsApp (nameToExp "return") (nameToExp (show i))))) ds) : (rewriteAlts (i+1) as)
           = (HsAlt s p (HsBody (nameToExp (show i))) ds) : (rewriteAlts (i+1) as)
       rewriteAlts i ((HsAlt s p (HsGuard (e:es)) ds):as)
        --  = (HsAlt s p (HsBody (Exp (HsApp (nameToExp "return") (nameToExp (show i))))) ds) : (rewriteAlts (i+1) as)
           = (HsAlt s p (HsBody  (nameToExp (show i))) ds) : (rewriteAlts (i+1) as)
       -- rewriteAlts i ((HsAlt s p (HsGuard (


addExpression pnt e (_,_,t)
 = do
      mod <- addExpression' pnt e t
      return mod

addExpression' pnt e t
  = applyTP (full_tdTP (idTP `adhocTP` inDec)) t
     where
       inDec (dec@(Dec (HsFunBind s matches))::HsDeclP)
         | findPNT pnt matches
             = do
                  let match@(HsMatch loc name pats rhs ds) = getMatch pnt matches

                  -- try and evaluate the highlighted expression
                  -- first let's transform the case so that each pattern match returns
                  -- a number, we can then use this to determine which
                  -- clause has suceeded.
                  (free,decs) <- hsFreeAndDeclaredNames match

                  newExp       <- rewriteCase e (rmGuard rhs)
                  let (newFun, newName) = createFun name (free++decs) pats (HsBody newExp) ds
                      newPats   = map createCall pats

                  addDecl t (Just (pNTtoPN name)) ([newFun], Nothing) True
                  return dec
       inDec (dec@(Dec (HsPatBind s p rhs ds)))
        | findPNT pnt p
            = do
                  -- let match@(HsMatch loc name pats rhs ds) = getMatch pnt matches

                  -- try and evaluate the highlighted expression
                  -- first let's transform the case so that each pattern match returns
                  -- a number, we can then use this to determine which
                  -- clause has suceeded.
                  (free,decs) <- hsFreeAndDeclaredNames dec

                  newExp       <- rewriteCase e rhs
                  let (newFun, newName) = createFun (patToPNT p) (free++decs) [] newExp ds
                      newPats   = map createCall []

                  addDecl t (Just (patToPN p)) ([newFun], Nothing) True
                  return dec


       inDec x = return x

       createCall (Pat (HsPList  s pats)) = (Pat (HsPList s (map createCall pats)))
       createCall p@(Pat (HsPLit _ _)) = p
       createCall (Pat (HsPAsPat _ p))
        = createCall p
       createCall p = error $ show p

       createFun name names pats newExp ds
        = (Dec (HsFunBind loc0 [HsMatch loc0 (nameToPNT newName) pats newExp ds]), newName)
         where
           newName = mkNewName (pNTtoName name) names 0

       rewriteCase :: (Term t, MonadPlus m) => HsExpP -> t -> m t
       rewriteCase e
         = applyTP (once_tdTP (failTP `adhocTP` (inExp e)))

       inGen e (HsLetStmt ds more) = do
                                      rest <- inGen e more
                                      return (HsLetStmt ds rest)
       inGen e x@(HsLast e1) = do
                                  e1' <- inExp e e1
                                  return (HsLast e1')
       inGen e (HsQualifier e1 more) = do
                                      rest <- inGen e more
                                      e1' <- inExp e e1
                                      return (HsQualifier e1' rest)
       inGen e (HsGenerator s p e1 more)
                                  = do
                                       rest <- inGen e more
                                       e1' <- inExp e e1
                                       return (HsGenerator s p e1' rest)
       inExp e x@(Exp (HsDo stmts)) = do
                                         stmts' <- inGen e stmts
                                         return (Exp (HsDo stmts'))

       inExp e x@(Exp (HsApp (Exp (HsParen e1)) e2))
         = do -- rewrite the case in x
             newX <- rewriteCase2 e x
             return newX
              where
                rewriteCase2 :: (Term t, MonadPlus m) => HsExpP -> t -> m t
                rewriteCase2 e
                  = applyTP (once_tdTP (failTP `adhocTP` (inExp2 e)))

                inExp2 x@(Exp (HsCase e alts)) y
                 | sameOccurrence x y = return (Exp (HsCase e (rewriteAlts 0 alts)))
                inExp2 e1 _ = mzero

       inExp e (Exp (HsLambda ps e2)) = do
                                           res <- inExp e e2
                                           return (Exp (HsLambda ps res))
       inExp e (Exp (HsLet ds e2)) = do
                                        res <- inExp e e2
                                        return (Exp (HsLet ds res))
       inExp e (Exp (HsParen e2)) = do
                                        res <- inExp e e2
                                        return (Exp (HsParen res))
       inExp (Exp (HsCase e alts)) e2 = do

                                          return (Exp (HsCase e (rewriteAlts 0 alts)))

       inExp e1 e2 = return e1

       rewriteAlts i [] = []
       rewriteAlts i ((HsAlt s p (HsBody e) ds):as)
        -- = (HsAlt s p (HsBody (Exp (HsApp (nameToExp "return") (nameToExp (show i))))) ds) : (rewriteAlts (i+1) as)
         = (HsAlt s p (HsBody  (nameToExp (show i))) ds) : (rewriteAlts (i+1) as)
       rewriteAlts i ((HsAlt s p (HsGuard (e:es)) ds):as)
        --  = (HsAlt s p (HsBody (Exp (HsApp (nameToExp "return") (nameToExp (show i))))) ds) : (rewriteAlts (i+1) as)
         = (HsAlt s p (HsBody (nameToExp (show i))) ds) : (rewriteAlts (i+1) as)

       -- rewriteAlts i ((HsAlt s p (HsGuard (

-- utility functions
getMatch :: PNT -> [HsMatchP] -> HsMatchP
getMatch _ [] = error "Please select a case in top-level expression scope!"
getMatch pnt (match@(HsMatch loc name pats rhs ds):ms)
  | useLoc pnt == useLoc name      = match
  | otherwise        = getMatch pnt ms


-- ---------------------------------------------------------------------

{-
ghcEvalExpr
  :: (Monad (t m), MonadTrans t,
      AbstractIO.StdIO m,
      AbstractIO.FileIO m) =>
     String -> String -> String -> t m [Char]
-}
{-
ghcEvalExprNew
  ::(Functor (t m), MonadCatchIO (t m), -- For evalExpr
     Monad (t m), MonadTrans t,
      AbstractIO.StdIO m,
      AbstractIO.FileIO m) =>
     String -> String -> String -> t m [Char]
-- ghcEvalExpr :: String -> String -> String -> IO String
ghcEvalExprNew fileName closure_call modName = do
  lift $ AbstractIO.putStrLn $ ("ghcEvalExpr[" ++ closure_call ++ "]1")
  res <- Evaluate.evalExpr fileName closure_call modName
  lift $ AbstractIO.putStrLn $ ("ghcEvalExpr[" ++ closure_call ++ "]=" ++ show(res))
  let res = Right "0"
  case res of
    Left err -> do
      -- Evaluate.printInterpreterError err
      return ("-1")
    Right x -> do
      -- AbstractIO.putStrLn $ show (x)
      lift $ AbstractIO.putStrLn $ ("ghcEvalExpr[" ++ closure_call ++ "]=" ++ show (x))
      return x
      -- return ("0")
-}
-- ---------------------------------------------------------------------
      
ghcEvalExpr
  :: (Monad (t m), MonadTrans t, AbstractIO.StdIO m,
      AbstractIO.FileIO m) =>
     String -> String -> String -> t m [Char]
ghcEvalExpr x y z = do
                       lift $ AbstractIO.putStrLn $ ("RefacSimplify.ghcEvalExpr:" ++ evaluate ++ ":" ++ evaluate_result ++ ":" ++ show ([x,y,z])) -- ++AZ++ 
                       let res = unsafePerformIO $ rawSystem evaluate [x,y,z] --   :: String -> [String] -> IO ExitCode
                       lift $ AbstractIO.putStrLn $ show res
                       res2 <- lift $ AbstractIO.readFile evaluate_result
                       case res of
                         (ExitFailure _) -> do
                                               error "The simplification could not be performed, some of the formals to the highlighted expression may not be well-defined."
                                               return "-1"
                         -- ++AZ++ _  -> do --lift $ AbstractIO.putStrLn $ show res2
                         _  -> do lift $ AbstractIO.putStrLn $ show res2
                                  return res2

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
             = if isSimplePatBind pat
                then Just (Patt, patToPNT ps, [], locToExp beginPos endPos toks rhs, ds)
                else error "A complex pattern binding can not be simplified!"
      inPat _ = Nothing


-- concatMapWithSpace :: (String -> String) -> [String] -> String
concatMapWithSpace f [] = " "
concatMapWithSpace f (x:xs) = ((f x) ++ " ") ++ concatMapWithSpace f xs

rmGuard ((HsGuard gs)::RhsP)
  = let (_,e1,e2)=glast "guardToIfThenElse" gs
               in  if ((pNtoName.expToPN) e1)=="otherwise"
                   then (foldl mkIfThenElse e2 (tail(reverse gs)))
                   else (foldl mkIfThenElse defaultElse (reverse gs))

    where
      mkIfThenElse e (_,e1, e2)=(Exp (HsIf e1 e2 e))

      defaultElse=(Exp (HsApp (Exp (HsId (HsVar (PNT (PN (UnQual "error") (G (PlainModule "Prelude") "error"
                    (N (Just loc0)))) Value (N (Just loc0)))))) (Exp (HsLit loc0 (HsString "UnMatched Pattern")))))
rmGuard (HsBody e) = e
