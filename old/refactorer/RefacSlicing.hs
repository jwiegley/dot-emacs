-----------------------------------------------------------------------------
-- |
-- Module      :  RefacSlicing
-- Copyright   :  (c) Christopher Brown 2005
--
-- Maintainer  :  cmb21@kent.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- This module contains a transformation for HaRe.
-- Symoblic Evaluation on tuples.
-- creates functions which evaluate tha expressions
-- within the return value of a function.
--  e.g.
--
-- @ f x y = (x, y) @
--
-- @ f1 x = x @
--
-- @ f2 y = y @
--
-----------------------------------------------------------------------------

module RefacSlicing where


import AbstractIO
import Data.Maybe
import Data.List
import RefacUtils
import RefacRedunDec
import SlicingUtils

data Patt = Match HsMatchP | MyPat HsDeclP | Def [Char]

refacSlicing args
  = do let
           fileName    = args!!0
           beginRow   = read (args!!1)::Int
           beginCol   = read (args!!2)::Int
           endRow     = read (args!!3)::Int
           endCol     = read (args!!4)::Int
       AbstractIO.putStrLn "refacSlicing"

       -- Parse the input file.
       modInfo@(inscps, exps, mod, tokList) <- parseSourceFile fileName

       -- Find the function that's been highlighted as the refactree

       let (loc, pnt, pats, exp, wh, p)
             = findDefNameAndExp tokList
                                 (beginRow, beginCol)
                                 (endRow, endCol)
                                 mod

       let newExp = locToExp (beginRow, beginCol) (endRow, endCol) tokList mod

       let transExp = rewriteExpression exp newExp

       if newExp == defaultExp
            then do
               error "Program slicing can only be performed on an expression."
            else do
               (wh', newExp') <- doRefac wh transExp

               -- ((_,_), (tokList', mod')) <- applyRefac (checkCase exp newExp wh') (Just inscps, exps, mod, tokList) fileName

               -- AbstractIO.putStrLn $ show (newExp, wh'')

               (_,refWh) <- checkCase exp newExp wh'

               -- (mod',((tokList',modified),_))<-doRemovingWhere fileName mod tokList exp newExp' wh'


               ((_,_), (tokList', mod')) <- applyRefac (doRemovingWhere exp newExp' refWh) (Just (inscps, exps, mod, tokList)) fileName

               ((_,m), (tokList'', mod'')) <- applyRefac (doRemoving1 exp  newExp' wh) (Just (inscps, exps, mod', tokList')) fileName

               -- ((_,_), (newTokList, newMod)) <- applyRefac (doTranslation exp transExp) (Just (inscps, exps, mod'', tokList'')) fileName

               -- AbstractIO.putStrLn $ show tokList''
               writeRefactoredFiles False [((fileName, True), (tokList'', mod''))]

               AbstractIO.putStrLn "Completed.\n"


doTranslation e nT (_,_,mod)
  = do
       newMod <- update e nT mod
       return newMod

sliceSubExp p old exp wh loc pnt pats (_,_, mod) = do

                                                 (decls, newExp) <- removeRedun wh exp

                                                 mod' <- updating p mod loc pnt pats newExp decls

                                                 return mod'

changeName newName (PNT (PN (UnQual _) (G modName _ optSrc)) Value s)
                  = PNT (PN (UnQual newName) (G modName newName optSrc)) Value s

updating (match@(Match x)) mod loc pnt pats rhs ds = do
                                                       mod' <- update x (newMatch loc pnt pats rhs ds) mod
                                                       return mod'
updating (pat@(MyPat x)) mod loc pnt pats rhs ds = do
                                                      mod' <- update x (newDecl loc pnt pats rhs ds) mod
                                                      return mod'

newMatch loc pnt pats rhs ds = HsMatch loc pnt pats (HsBody rhs) ds
newDecl loc pnt pats rhs ds = Dec (HsFunBind loc [HsMatch loc pnt pats (HsBody rhs) ds] )

checkFreeInWhere :: [PName] -> [HsDeclP] -> [HsDeclP]
checkFreeInWhere [] _ = []
checkFreeInWhere _ [] = []
checkFreeInWhere (p:ps) list = (checkSinInWhere p list) ++ (checkFreeInWhere ps list)
                                 where
                                   checkSinInWhere :: PName -> [HsDeclP] -> [HsDeclP]
                                   checkSinInWhere p [] = []
                                   checkSinInWhere p (x:xs)
                                      | defines p x = [x]
                                      | otherwise   = checkSinInWhere p xs


rewriteExpression :: HsExpP -> HsExpP -> HsExpP
rewriteExpression e@(Exp (HsInfixApp e1 o e2)) newExp
 | findEntity newExp e1 = (rewriteExpression e1 newExp)
 | findEntity newExp e2 = (rewriteExpression e2 newExp)
 | otherwise = e
rewriteExpression (Exp (HsLet ds e)) newExp = (Exp (HsLet ds (rewriteExpression e newExp)))
rewriteExpression (Exp (HsLambda ds e)) newExp = (Exp (HsLambda ds newExp))
rewriteExpression (Exp (HsParen e1)) newExp = rewriteExpression e1 newExp
rewriteExpression e1 e2 = e2

{-|
Takes the position of the highlighted code and returns
the function name, the list of arguments, the expression that has been
highlighted by the user, and any where\/let clauses associated with the
function.
-}

{-findDefNameAndExp :: Term t => [PosToken] -- ^ The token stream for the
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
findDefNameAndExp toks beginPos endPos t
  = fromMaybe ([], defaultPNT, [], defaultExp, [], Def [])
              (applyTU (once_tdTU (failTU `adhocTU` inMatch `adhocTU` inPat)) t)

    where
      --The selected sub-expression is in the rhs of a match
      inMatch (match@(HsMatch loc1  pnt pats (rhs@(HsBody e)) ds)::HsMatchP)
        | locToExp beginPos endPos toks rhs /= defaultExp
          = Just ([loc1], pnt, pats, e, ds, (Match match))
      inMatch _ = Nothing

      --The selected sub-expression is in the rhs of a pattern-binding
      inPat (pat@(Dec (HsPatBind loc1 ps (rhs@(HsBody e)) ds))::HsDeclP)
        | locToExp beginPos endPos toks rhs /= defaultExp
          = if isSimplePatBind pat
              then Just ([loc1], patToPNT ps, [], e, ds, (MyPat pat))
              else error "A complex pattern binding can not be generalised!"
      inPat _ = Nothing



