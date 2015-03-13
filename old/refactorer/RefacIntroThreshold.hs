module RefacIntroThreshold (refacIntroThreshold) where
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
import Debug.Trace
import RefacMvDefBtwMod (addImport)
import LocalSettings (evalFilePath)
import RefacGenDef (generaliseDef2)

refacIntroThreshold args =
  do let fileName = args!!0
         thresholdValue = args!!1
         thresholdName  = args!!2
         beginRow = read (args!!3)::Int
         beginCol = read (args!!4)::Int
         endRow   = read (args!!5)::Int
         endCol   = read (args!!6)::Int
     -- modName <- fileNameToModName fileName

     (inscps, exps, mod, tokList) <- parseSourceFile fileName

     unless ( isHidden ["rseq", "rpar", "runEval"] (concat  (findImportsHiddenLists mod)) == [] )
          $ error "rseq, rpar and/or runEval are explicitly hidden. Please unhide and try again."

     let theSeq = checkForQualifiers "rseq" inscps
         theRPar = checkForQualifiers "rpar" inscps
         expr = grabSelection (beginRow, beginCol) (endRow, endCol) tokList mod

     fileContent <- AbstractIO.readFile evalFilePath

     unless (fileContent /= []) $ error "No active eval monad! Please activate an evaluation monad to continue!"

     let runEval = read (fileContent) :: HsPatP

     -- add the threshold to the function...
     (m, tokList', mod', refactoredClients) <- generaliseDef2 fileName thresholdName (beginRow, beginCol) (endRow, endCol) (nameToExp thresholdValue) inscps exps mod tokList


     AbstractIO.putStrLn $ show (length refactoredClients)

     ((_,m'), (newToks, newMod)) <- applyRefac (doIntroduce expr thresholdValue thresholdName runEval theRPar theSeq) (Just (inscps, exps, mod', tokList')) fileName

     -- writeRefactoredFiles True [((fileName, m), (newToks, newMod))]

     writeRefactoredFiles False $ ((fileName, m'), (newToks, newMod)):refactoredClients

     AbstractIO.putStrLn "refacIntroThreshold Completed."

checkForQualifiers r inscps
  = ck1 r inscps
 where
      ck1 r i
       | isInScopeAndUnqualified r i = r
       | length res == 0 = r
       | length res > 1 = error (r ++ " is qualified more than once. " ++ r ++ " must only be qualified once or not at all to proceed.")
       | otherwise      = if res /= [] then (modNameToStr (head res)) ++"."++ r else r
          where res = hsQualifier2 (nameToPNT r) i

addTheImport ss mod
  = addImport "" (strToModName "Control.Parallel.Strategies") (map nameToPN ss) mod

isHidden [] ys = []
isHidden (x:xs) ys
  | elem x ys = x : isHidden xs ys
  | otherwise = isHidden xs ys

findImportsHiddenLists
  = applyTU (full_tdTU (constTU [] `adhocTU` inImport))
    where
      inImport (HsImportDecl loc modName qual _ (Just (True, h))::HsImportDeclP) = return ((map (\(Var x) -> (pNTtoName x))) h)
      inImport _ = return []

grabSelection pos1 pos2 toks mod
  | expr == defaultExp = if pat == defaultPat then error "Select pattern/sub-expr is not valid for thresholding!"
                                              else pNtoExp (patToPN pat)
  | otherwise          = expr
    where
      expr = locToExp pos1 pos2 toks mod
      pat = locToPat pos1 pos2 toks mod

doIntroduce expr thresholdValue thresholdName runEval theRPar theSeq (_, _, t)
  = do mod <- doIntroduce' expr thresholdValue thresholdName runEval theRPar theSeq t
       if mod == t
        then return t
        else do
               mod' <- addTheImport [theSeq] mod
               return mod'

doIntroduce' expr thresholdValue thresholdName runEval theRPar theSeq t
 = applyTP (once_buTP (failTP `adhocTP` inMatch) `choiceTP` failure) t
  where

    -- has to be a match: generalising already converted pattern bindings
    -- to a match
    inMatch (match@(HsMatch l name pats rhs ds)::HsMatchP)
     |  findEntity expr match
     && runEval `myElem` ds
       = do (f,d) <- hsFDNamesFromInside match
            -- error (show ((f++d), thresholdName))
            -- unless (not (thresholdName `elem` (f++d))) $ error "Error: name of threshold parameter is already used on RHS!"
            let runEval' = findPat runEval ds
            if runEval' == Nothing
               then mzero
               else do
                       let  newName = mkNewName "rpar_abs" (f++d) 1
                            newRunEval = modifyRunEval expr thresholdValue thresholdName newName theRPar theSeq (fromJust runEval')
                       -- match' <- addDecl match Nothing ([newParAbs], Nothing) False
                       match'' <- update (fromJust runEval') newRunEval match

                       return match''

    inMatch _ = mzero

    -- inModule (mod::HsModuleP)
    --  | isDeclaredIn (

    failure = idTP `adhocTP` mod
      where mod (m::HsModuleP) = error "Cannot find the activated Eval Monad! Please activate a run eval monad within scope of the selected entity."

    modifyRunEval expr thresholdValue thresholdName newName theRPar theSeq (pat@(Dec (HsPatBind l p rhs ds)))
     = Dec (HsPatBind l p (convertToSeq newName rhs) (ds++[mkParAbs newName theRPar theSeq]))   -- (Dec (HsPatBind l p (addGuards rhs) ds))
      {-   where



            addGuards (HsGuard es) = error "Cannot add threshold to an eval monad with guards already defined!"
            addGuards (HsBody e) = 	HsGuard [(loc0, theGuard, convertToSeq e), (loc0, nameToExp "otherwise", e)]
            theGuard = Exp (HsInfixApp expr (theOpp) (nameToExp thresholdName))
            theOpp   = HsVar (nameToPNT "<")
        -}

    mkParAbs name theRPar theRSeq = (Dec (HsPatBind loc0 (nameToPat name) addGuards []))
     where
      addGuards = HsGuard [(loc0, theGuard, nameToExp theRPar), (loc0, nameToExp "otherwise", nameToExp theRSeq)]
      theGuard = Exp (HsInfixApp expr (theOpp) (nameToExp thresholdName))
      theOpp   = HsVar (nameToPNT ">")

    convertToSeq :: (Term t) => String -> t -> t
    convertToSeq newName e
      = runIdentity (applyTP (full_tdTP (idTP `adhocTP` exp)) e)
       where
        exp (Exp (HsId (HsVar i))::HsExpP)
         | pNTtoName i == "rpar" = return $ nameToExp newName
        exp x = return x

    findPat :: HsPatP -> [HsDeclP] -> Maybe HsDeclP
    findPat p [] = Nothing -- error "Cannot find active Eval Monad pattern binding!"
    findPat p ((Dec (HsFunBind s m)):ds) = findPat p ds
    findPat p (a@(Dec (HsPatBind l p2 rhs _)):ds)
      | p == p2 = Just $ a
      | otherwise = findPat p ds
    findPat p (_:ds) = findPat p ds

    myElem :: HsPatP -> [HsDeclP] -> Bool
    myElem p [] = False
    myElem p ((Dec (HsFunBind s m)):ds) = myElem p ds
    myElem p ((Dec (HsPatBind l p2 rhs _)):ds)
      | p == p2 = True
      | otherwise = myElem p ds
    myElem p (_:ds) = myElem p ds
