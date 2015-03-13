
-- ++AZ++ NOTE: this file has changed since 0.6.0.2
-----------------------------------------------------------------------------
-- |
-- Module      :  RefacLetWhere
-- Copyright   :  (c) Christopher Brown 2008
--
-- Maintainer  :  cmb21@kent.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- This module contains a transformation for HaRe.
-- Let to Where and its converse. Apart from the pure syntactic change,
-- A where is an equation where a let is an expression. Therefore, one must
-- take into account guards and patterns as well as scoped entities.
--
-- Let also binds closer than Where.
--
-----------------------------------------------------------------------------

module RefacLetWhere where

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

data LetType = LetExp HsExpP | MonExp HsStmtP | Gen [HsDeclP]

letToWhere args
 = do let  fileName = ghead "filename"  args
           row = read (args!!1)::Int
           col = read (args!!2)::Int
      -- f <-  MT.lift $ getCurrentDirectory
      modName <- fileNameToModName fileName
      (inscps, _, mod, toks) <- parseSourceFile fileName
      let pnt = locToPNT fileName (row, col) mod
          pn = pNTtoPN pnt
      if pn /= defaultPN
         then liftToWhere modName fileName (inscps, mod, toks) pnt
         else error "\nInvalid cursor position!\n"


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
                  -> (PNT, FunctionPats, HsExpP, WhereDecls) -- ^ A tuple of,
                     -- (the function name, the list of arguments,
                     -- the expression highlighted, any where\/let clauses
                     -- associated with the function).

findDefNameAndExp toks beginPos endPos t
  = fromMaybe (defaultPNT, [], defaultExp, [])
              (applyTU (once_tdTU (failTU `adhocTU` inMatch `adhocTU` inPat)) t)

    where
      --The selected sub-expression is in the rhs of a match
      inMatch (match@(HsMatch loc1  pnt pats rhs ds)::HsMatchP)
        | locToExp beginPos endPos toks rhs /= defaultExp
          = Just (pnt, pats, locToExp beginPos endPos toks rhs, ds)
      inMatch _ = Nothing

      --The selected sub-expression is in the rhs of a pattern-binding
      inPat (pat@(Dec (HsPatBind loc1 ps rhs ds))::HsDeclP)
        | locToExp beginPos endPos toks rhs /= defaultExp
          = Just (patToPNT ps, [], locToExp beginPos endPos toks rhs, ds)
      inPat _ = Nothing



convertLets d e (_,_,mod)
 = do
      t' <- addLetInWhere d e mod
      t''  <- doLetToWhere d e t'
      return t''

liftToWhere modName fileName (inscps, mod, toks) pnt@(PNT pn _ _)
  = if isLocalFunOrPatName pn mod
        then do (mod', ((toks',m),_))<-liftWhereLevel
                writeRefactoredFiles False [((fileName,m),(toks',mod'))]
        else error "\nThe identifer is not a function/pattern name!"
   where
    liftWhereLevel =
       runStateT (applyTP ((once_tdTP (failTP `adhocTP` liftToWhere'
                                                            `adhocTP` liftToWhere'
                                                            ))
                                          `choiceTP` failure) mod) ((toks,unmodified),(-1000,0))
         where
           liftToWhere' (pat@(Dec (HsPatBind loc p rhs ds))::HsDeclP)
             | definingDecls [pn] (hsDecls rhs) False  False /=[]
                  =doLifting2 pat  pn
           liftToWhere' _=mzero

           doLifting2 dest@(Dec (HsPatBind loc p parent ds)) pn
               = do  let  liftedDecls=definingDecls [pn] (hsDecls parent) True  False
                          declaredPns=nub $ concatMap definedPNs liftedDecls
                     pns<-pnsNeedRenaming inscps dest parent liftedDecls declaredPns
                     (_, dd)<-hsFreeAndDeclaredPNs dest
                     if pns==[]
                       then do (parent',liftedDecls',paramAdded)<-addParamsToDef pn dd parent liftedDecls
                               let liftedDecls''=if paramAdded then filter isFunOrPatBind liftedDecls'
                                                                else liftedDecls'
                               moveDecl1 (Dec (HsPatBind loc p parent' ds)) Nothing [pn] False
                         else askRenamingMsg pns "lifting"

           worker dest ds pn
                  =do let (before, parent,after)=divideDecls ds pnt
                          liftedDecls=definingDecls [pn] (hsDecls parent) True  False
                          declaredPns=nub $ concatMap definedPNs liftedDecls
                      (_, dd)<-hsFreeAndDeclaredPNs dest
                      pns<-pnsNeedRenaming inscps dest parent liftedDecls declaredPns
                      if pns==[]
                        then do
                                (parent',liftedDecls',paramAdded)<-addParamsToDef pn dd
                                                                     parent liftedDecls
                                let liftedDecls''=if paramAdded then filter isFunOrPatBind liftedDecls'
                                                                else liftedDecls'
                                --True means the new decl will be at the same level with its parant.
                                dest'<-moveDecl1 (replaceDecls dest (before++parent'++after))
                                           (Just (ghead "liftToWhere" (definedPNs (ghead "worker" parent')))) [pn] False
                                return (hsDecls dest')
                                --parent'<-doMoving declaredPns (ghead "worker" parent) True  paramAdded parent'
                                --return (before++parent'++liftedDecls''++after)
                        else askRenamingMsg pns "lifting"

           failure=idTP `adhocTP` mod
                where
                  mod (m::HsModuleP)
                   = error ( "Lifting this definition failed. "++
                           " This might be because that the definition to be lifted is defined in a class/instance declaration.")

--return True if pn is a local function/pattern name
isLocalFunOrPatName pn scope
 =isLocalPN pn && isFunOrPatName pn scope

-- |Divide a declaration list into three parts (before, parent, after) according to the PNT,
-- where 'parent' is the first decl containing the PNT, 'before' are those decls before 'parent'
-- and 'after' are those decls after 'parent'.

divideDecls::[HsDeclP]->PNT->([HsDeclP],[HsDeclP],[HsDeclP])
divideDecls ds pnt
  = let (before,after)=break (\x->findPNT pnt x) ds
    in if (after/=[])
         then (before, [ghead "divideDecls" after], tail after)
         else (ds,[],[])


--Get the subset of 'pns' that need to be renamed before lifting.
pnsNeedRenaming inscps dest parent liftedDecls pns
   =do r<-mapM pnsNeedRenaming' pns
       return (concat r)
  where
     pnsNeedRenaming' pn
       = do (f,d)<-hsFDsFromInside dest  --f: free variable names that may be shadowed by pn
                                             --d: declaread variables names that may clash with pn
            vs<-hsVisiblePNs pn parent      --vs: declarad varaibles that may shadow pn
            let inscpNames = map (\(x,_,_,_)->x) $ inScopeInfo inscps
                vars = map pNtoName (nub (f `union` d `union` vs) \\ [pn]) -- `union` inscpNames
            if elem (pNtoName pn) vars  || isInScopeAndUnqualified (pNtoName pn) inscps && findEntity pn dest
               then return [pn]
               else return []
     --This pNtoName takes into account the qualifier.
     pNtoName (PN (UnQual i) orig)=i
     pNtoName (PN (Qual (PlainModule modName) i ) orig)=modName ++ "." ++ i


askRenamingMsg pns str
  = error ("The identifier(s):" ++ showEntities showPNwithLoc pns ++
           " will cause name clash/capture or ambiguity occurrence problem after "
           ++ str ++", please do renaming first!")

moveDecl1 t defName pns topLevel
   = do ((toks, _),_)<-get
        let (declToMove, toksToMove) = getDeclAndToks (ghead "moveDecl1" pns) True toks t
	--error$ show (declToMove, toksToMove)
        t' <- rmDecl (ghead "moveDecl3"  pns) False =<<foldM (flip rmTypeSig) t pns
        addDecl t' defName (declToMove, Just toksToMove) topLevel


{-
LiftToWhere' d (LetExp le@(Exp (HsLet xs e1))) t
  = applyTP (stop_tdTP (failTP `adhocTP` funcCheck)) t
     where
       funcCheck (dec@(Dec (HsPatBind l ps rhs ds))::HsDeclP)
         | findEntity le rhs = do
                                  (gg, decsRHS) <- freeDecs' rhs

                                  when (length (filter (==(declToPName2 d)) decsRHS) > 1)
                                       (error ("Please rename " ++ (declToName d) ++ "before this refactoring to resolve scoping issues."))

                                  (free, decs) <- freeDecs ds
                                  if (declToName d) `elem` decs
                                     then do
                                       error ("Lifting " ++ (declToName d) ++
                                              " conflicts with a declared entity in the where clause. Please rename the entity first.")
                                     else do

                                           -- then we pass in the dependencies as parameters! :)
                                           let liftedDecls=definingDecls [(declToPName2 d)] [dec] True True
                                           (_,dd)<-hsFreeAndDeclaredPNs t
                                           op@(declToLift, ds', md) <- addParamsToDef (declToPName2 d) dd dec liftedDecls
                                           error $ show op
                                           {- let freeDec' = filterDecs freeDec (freeLet ++ decLet)
                                           error ( (concat (map pNtoName freeDec')) ++
                                                   " is/are not in scope within in the where clause.") -}
         | otherwise         = return dec
           where
       funcCheck (dec@(Dec (HsFunBind loc matches))::HsDeclP)
        = do
             result <- checkMatches matches
             return (Dec (HsFunBind loc result))
          where
            checkMatches [] = return matches
            checkMatches (m@(HsMatch _ _ _ rhs ds):ms)
              |  findEntity le rhs = do
                                      decsRHS <- (decsInRHS rhs)
                                      when (length (filter (==(declToName d)) decsRHS) > 1)
                                            (error ("Please rename " ++ (declToName d) ++ "before this refactoring to resolve scoping issues."))


                                      (free, decs) <- freeDecs ds
                                      if (declToName d) `elem` decs
                                       then do
                                        error ("Lifting " ++ (declToName d) ++
                                               " conflicts with a declared entity in the where clause. Please rename the entity first.")
                                       else do
                                        (freeDec, _) <- freeDecs' d
                                        (freeLet, decLet) <- freeDecs' (xs \\ [d])
                                        (free', decs') <- freeDecs' ds

                                        if and (freeDec `myElem` decLet) && and (freeDec `myElem` (freeLet ++ decLet))
                                         then do
                                          ds' <- addDecl m Nothing ([d], Nothing) False
                                          return (ds':ms)
                                         else do
                                           let freeDec' = filterDecs freeDec (freeLet ++ decLet)
                                           error ( (concat (map pNtoName freeDec')) ++
                                                   " is/are not in scope within in the where clause.")
              | otherwise = do
                               rest <- checkMatches ms
                               return (m:rest)
                  where
                   freeDecs m = hsFreeAndDeclaredNames m
       funcCheck x = return x

       decsInRHS rhs
         = do (_, res) <- hsFreeAndDeclaredNames rhs
              return res

       freeDecs m = hsFreeAndDeclaredNames m
       freeDecs' m = hsFreeAndDeclaredPNs m
       filterDecs [] [] = []
       filterDecs [] _  = []
       filterDecs _ []  = []
       filterDecs (x:xs) list
               | x `elem` list = x : filterDecs xs list
               | otherwise     = filterDecs xs list

       myElem [] [] = [True]
       myElem [] _  = [True]
       myElem _ []  = [True]
       myElem (x:xs) list = (x `elem` xs) : myElem xs list        -}

addLetInWhere d (MonExp le@(HsLetStmt xs r)) t
  = applyTP (stop_tdTP (failTP `adhocTP` funcCheck)) t
     where
       funcCheck (dec@(Dec (HsPatBind l ps rhs ds))::HsDeclP)
         | findEntity le rhs = do
                                  (free, decs) <- freeDecs ds
                                  if (declToName d) `elem` decs
                                     then do
                                       error ("Lifting " ++ (declToName d) ++
                                              " conflicts with a declared entity in the where clause. Please rename the entity first.")
                                     else do
                                       (freeDec, _) <- freeDecs' d
                                       (freeLet, decLet) <- freeDecs' (xs \\ [d])
                                       (free', decs') <- freeDecs' ds

                                       if and (freeDec `myElem` decLet) && and (freeDec `myElem` (freeLet ++ decLet))
                                         then do
                                           ds' <- addDecl dec Nothing ([d], Nothing) False
                                           return ds'
                                         else do
                                           let freeDec' = filterDecs freeDec (freeLet ++ decLet)
                                           error ( (concat (map pNtoName freeDec')) ++
                                                   " is/are not in scope within in the where clause.")
         | otherwise         = return dec
           where
       funcCheck (dec@(Dec (HsFunBind loc matches))::HsDeclP)
        = do
             result <- checkMatches matches
             return (Dec (HsFunBind loc result))
          where
            checkMatches [] = return matches
            checkMatches (m@(HsMatch _ _ _ rhs ds):ms)
              |  findEntity le rhs = do
                                      (free, decs) <- freeDecs ds
                                      if (declToName d) `elem` decs
                                       then do
                                        error ("Lifting " ++ (declToName d) ++
                                               " conflicts with a declared entity in the where clause. Please rename the entity first.")
                                       else do
                                        (freeDec, _) <- freeDecs' d
                                        (freeLet, decLet) <- freeDecs' (xs \\ [d])
                                        (free', decs') <- freeDecs' ds

                                        if and (freeDec `myElem` decLet) && and (freeDec `myElem` (freeLet ++ decLet))
                                         then do
                                          ds' <- addDecl m Nothing ([d], Nothing) False
                                          return (ds':ms)
                                         else do
                                           let freeDec' = filterDecs freeDec (freeLet ++ decLet)
                                           error ( (concat (map pNtoName freeDec')) ++
                                                   " is/are not in scope within in the where clause.")
              | otherwise = do
                               rest <- checkMatches ms
                               return (m:rest)
                  where
                   freeDecs m = hsFreeAndDeclaredNames m


       funcCheck x = return x


       freeDecs m = hsFreeAndDeclaredNames m
       freeDecs' m = hsFreeAndDeclaredPNs m
       filterDecs [] [] = []
       filterDecs [] _  = []
       filterDecs _ []  = []
       filterDecs (x:xs) list
               | x `elem` list = x : filterDecs xs list
               | otherwise     = filterDecs xs list

       myElem [] [] = [True]
       myElem [] _  = [True]
       myElem _ []  = [True]
       myElem (x:xs) list = (x `elem` xs) : myElem xs list
addLetInWhere _ _ _ = error "Please highlight a let expression!"

addParamsToDef pn dd parent liftedDecls
  =do  (ef,_)<-hsFreeAndDeclaredPNs parent
       (lf,_)<-hsFreeAndDeclaredPNs liftedDecls
       let newParams=((nub lf)\\ (nub ef)) \\ dd  --parameters (in PName format) to be added to pn because of lifting
       if newParams/=[]
         then if  (any isComplexPatBind liftedDecls)
                then error "This pattern binding cannot be lifted, as it uses some other local bindings!"
                else do parent'<-{-addParamsToDecls parent pn newParams True-} addParamsToParent pn newParams parent
                        liftedDecls'<-addParamsToDecls liftedDecls pn newParams True
                        return (parent', liftedDecls',True)
         else return (parent,liftedDecls,False)

addParamsToParent pn [] t = return t
addParamsToParent pn params t
   =applyTP(full_buTP (idTP  `adhocTP` inExp)) t
   where
          inExp (exp@(Exp (HsId (HsVar (PNT pname ty loc))))::HsExpP)
            | pname==pn
             = do  let newExp=Exp (HsParen (foldl addParamToExp exp (map pNtoExp params)))
                   update exp newExp exp

          inExp x =return x

          addParamToExp  exp param
              =(Exp (HsApp exp param))


doLetToWhere :: (MonadPlus m, Term t, MonadState (([PosToken], Bool), (Int, Int)) m) =>
                 HsDeclP -> LetType -> t -> m t
doLetToWhere d (LetExp e@(Exp (HsLet xs e1))) t
  =  applyTP (stop_tdTP (failTP `adhocTP` (expCheck e))) t
    where
      expCheck (exp1::HsExpP) (exp2::HsExpP)
        | sameOccurrence exp1 exp2 == True
           = do
                if (length xs) > 1
                  then do
                          ds <- rmDecl (pNTtoPN (declToPNT d)) False xs
                          return (Exp (HsLet ds e1))
                  else do
                          update exp2 e1 exp2
        | otherwise = mzero
doLetToWhere d (MonExp m@(HsLetStmt xs r)) t
  =  applyTP (stop_tdTP (failTP `adhocTP` (expCheck m))) t
    where
      expCheck (stmt1::HsStmtP) (stmt2::HsStmtP)
        | sameOccurrence stmt1 stmt2 == True
           = do
                if (length xs) > 1
                  then do
                          ds <- rmDecl (pNTtoPN (declToPNT d)) False xs
                          return (HsLetStmt ds r)
                  else do
                          update stmt1 r stmt1
        | otherwise = mzero
doLetToWhere _ _ _ = error "Please highlight a let expression!"


checkLet :: (Term t) => t -> PName -> LetType
checkLet t name
 = (fromMaybe (error "Please select a definition within a let clause"))
              (applyTU (once_buTU (failTU `adhocTU` inExp `adhocTU` inMon)) t)
    where
      inExp exp@(Exp (HsLet ds e)::HsExpP)
        | or (map (defines name) ds) = Just (LetExp exp)
      inExp _ = Nothing

      inMon mon@((HsLetStmt ds rest)::HsStmtP)
        | or (map (defines name) ds) = Just (MonExp mon)
      inMon _ = Nothing
      -- inMonad mon@(

checkCursor :: String -> Int -> Int -> HsModuleP -> HsDeclP
checkCursor fileName row col mod
 = (fromMaybe (error "Please select a definition!")) $ (locToDec fileName (row, col) mod)

-- |Find the declaration(in PNT format) whose start position is (row,col) in the
-- file specified by the fileName, and returns Nothing if such an identifier does not exist.

locToDec::(Term t)=>String      -- ^ The file name
                    ->(Int,Int) -- ^ The row and column number
                    ->t         -- ^ The syntax phrase
                    ->Maybe HsDeclP       -- ^ The result
locToDec  fileName (row, col) t
  =applyTU (once_buTU (failTU `adhocTU` worker)) t
     where
        worker dec@(Dec (HsFunBind loc ((HsMatch loc0 name p rhs ds):ms))::HsDeclP)
          | locToPNT' name fileName (row, col) = Just dec
        worker dec@(Dec (HsPatBind loc0 name rhs ds))
          | locToPNT' (patToPNT name) fileName (row, col) = Just dec
        worker _ = Nothing

        locToPNT' name fileName (row, col)
          = (fromMaybe False) $ (applyTU (once_buTU (failTU `adhocTU` worker)) name)
           where
            worker pnt@(PNT pname ty (N (Just (SrcLoc fileName1 _ row1 col1))))
              |fileName1==fileName && (row1,col1) == (row,col) = Just True
            worker _ =Nothing
