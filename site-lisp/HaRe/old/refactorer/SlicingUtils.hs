module SlicingUtils where

import AbstractIO
import Data.Maybe
import Data.List
import RefacUtils
import RefacRedunDec


checkCase (Exp(HsInfixApp e11 o e22 )) high wh
  | findEntity high e11 = do
                             (e, wh) <- checkCase e11 high wh
                             return (e, wh)
  | findEntity high e22 = do
                             (e, wh) <- checkCase e22 high wh
                             return (e,wh)

checkCase (Exp(HsParen e)) high wh 
                = do 
                     res <- checkCase e high wh
                     return res
checkCase (Exp(HsCase e alts)) high wh
                = do
                     newWhere <- checkAlts alts
                     return (high, (newWhere++wh))
                        where
                           checkAlts [] = do
                                             return []
                           checkAlts ((HsAlt _ _ _ ds):xs) 
                              = do
                                   decls <- removeRedunWhere ds high
                                   res <- checkAlts xs
                                   return (decls ++ res)

checkCase (exp@e) high wh  = do
                              decls <- removeRedunWhere wh e
                              return (exp, decls)


checkIfOrLet (Exp(HsParen e)) newExp tokList start end
                = do
                     res <- checkIfOrLet e newExp tokList start end
                     return (Exp(HsParen res))

checkIfOrLet (Exp(HsIf e1 e2 e3)) newExp tokList start end
                = do
                     let expRes = findExpInIf tokList
                                              start
                                              end
                                              e2
                     if expRes == defaultExp
                         then do
                                 let expRes' = findExpInIf tokList
                                                           start
                                                           end
                                                           e3
                                 if expRes' == defaultExp 
                                      then return (Exp(HsIf e1 e2 e3)) 
                                      else return (newExp)
                         else return (newExp)
checkIfOrLet (Exp(HsLet ds e)) newExp _ _ _ 
                = do
                     return (Exp(HsLet ds newExp))

checkIfOrLet (exp@_) newExp _ _ _ = do
                               return newExp
-- check whether the identifiers within the highlighted subexpression are 
-- used within the let statement - if they are then return the statement
checkLetAndLambda begin end tokList wh high exp
  = applyTU (full_tdTU (constTU [] `adhocTU` inLet)) exp
     where
           inLet (ex@(Exp(HsLet ds e))::HsExpP)
               = do 
                    let newExp = (Exp(HsLet ds high))
                    (decls, x) <- removeRedun wh newExp
                    res <- inLet e
                    if res == [defaultExp] then do
                                             return [x]
                                           else do
                                             let exp' = ammendDecs res x
                                             return [exp']
                                                where
                                                  ammendDecs ((Exp(HsLet ds e)):xs) ((Exp(HsLet decls e2))) 
                                                                 = (Exp(HsLet (decls++ds) e))
                                                  ammendDecs _ _ = defaultExp

           inLet (Exp(HsParen e)) = do res <- inLet e 
                                       return res
           inLet (Exp(HsInfixApp e1 _ e2)) = do
                                           res <- inLet e1
                                           if res == [defaultExp]
                                               then do
                                                  res' <- inLet e2
                                                  return res'
                                               else do
                                                  return res
           inLet (Exp(HsApp e1 e2)) = do
                                        res <- inLet e1
                                        if res == [defaultExp]
                                           then do
                                             res' <- inLet e2
                                             return res'
                                           else do
                                             return res
           inLet (Exp(HsCase e alts))
                = do 
                     return [(Exp(HsCase high alts))]

           inLet (exp@(Exp(HsDo _)))
               = do
                    if (locToExp begin end tokList exp) /= defaultExp
                       then do
                         error "Cannot perform a slicing on a monad"
                       else do return [exp] 

           inLet (exp@(Exp(HsListComp _))) = do
                                              if (locToExp begin end tokList exp) /= defaultExp
                                                then do
                                                  error "Cannot perform slicing with List Comprehension"
                                                else do return [defaultExp]

           inLet (_::HsExpP) = do
                                return [defaultExp]
                    

findExpInIf toks beginPos endPos t
  = fromMaybe (defaultExp)
              (applyTU (once_tdTU (failTU `adhocTU` inExp)) t)
        where
          inExp (exp@(_)::HsExpP)
           | locToExp beginPos endPos toks exp /= defaultExp
              = Just (exp)
          inExp _ = Nothing
          


