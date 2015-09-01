module RefacIntroEvalDegree (refacDeepSeq) where

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
-- import LocalSettings

refacDeepSeq args =
    do let fileName = args!!0
           beginRow = read (args!!1)::Int
           beginCol = read (args!!2)::Int
           endRow   = read (args!!3)::Int
           endCol   = read (args!!4)::Int

       (inscps, exps, mod, tokList) <- parseSourceFile fileName

       unless ( isHidden ["rdeepseq", "dot"] (concat  (findImportsHiddenLists mod)) == [] )
          $ error "rdeepseq and/or dot are explicitly hidden. Please unhide and try again."

       let theDeepSeq = checkForQualifiers "rdeepseq" inscps
           theDot = checkForQualifiers "dot" inscps
           expr = grabSelection (beginRow, beginCol) (endRow, endCol) tokList mod


       ((_,m'), (newToks, newMod)) <- applyRefac (doIntroduceDeepSeq theDeepSeq theDot expr) (Just (inscps, exps, mod, tokList)) fileName


       writeRefactoredFiles False [((fileName, m'), (newToks, newMod))]


       AbstractIO.putStrLn "refacDeepSeq Completed."

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

doIntroduceDeepSeq theRdeepSeq theDot e (_,_,t)
 = do mod <- doIntroduce' theRdeepSeq theDot e t
      mod' <- addTheImport [theRdeepSeq, theDot] mod
      return mod'

doIntroduce' theRdeepSeq theDot e t
 = applyTP (once_buTP (failTP `adhocTP` inExpr) `choiceTP` failure) t
   where
     inExpr (e2@(Exp _)::HsExpP)
      | sameOccurrence e e2 = do e2' <- update e2 (Exp (HsInfixApp e2 (HsVar (nameToPNT theDot)) (nameToExp theRdeepSeq))) e2
                                 return e2'
     inExpr _ = mzero


     failure = idTP `adhocTP` mod
       where mod (m::HsModuleP) = error "Cannot find the select sub-expression! Please select a valid sub-expression."
