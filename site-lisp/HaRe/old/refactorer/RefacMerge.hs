-----------------------------------------------------------------------------
-- |
-- Module      :  RefacMerge
-- Copyright   :  (c) Christopher Brown 2006
--
-- Maintainer  :  cmb21@kent.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- This module contains a transformation for HaRe.
-- Merging definitions together.


module RefacMerge where


import System.IO.Unsafe
import PrettyPrint
import RefacTypeSyn
import RefacLocUtils
-- import GHC (Session)
import Data.Char
import GHC.Unicode
import AbstractIO
import Data.Maybe
import Data.List
import RefacUtils
import RefacRedunDec
import SlicingUtils
import System.Directory
import LocalSettings (mergeFilePath)

data FunEntity = Guard [HsPatP] [(SrcLoc, HsExpP, HsExpP)] [HsDeclP] PNT | Match [HsPatP] HsExpP [HsDeclP] PNT | Null
                   deriving (Eq, Show)

type Fun = [ FunEntity ]

-- we can "pair" an arbitrary number of matches together so
-- we can't use a tuple. We don't know the number of
-- function to fuse!
type PairFun = [ Fun ]

refacMerge args
  = do
       let fileName     = args!!0
           name         = args!!1
       AbstractIO.putStrLn "refacMerge"

       fileContent <- AbstractIO.readFile mergeFilePath

       AbstractIO.removeFile mergeFilePath

       AbstractIO.putStrLn "Cache flushed."

       unless (isVarId name)
           $ error "The new name is invalid!\n"

       modName1 <- fileNameToModName fileName
       let modName = modNameToStr modName1

       modInfo@(inscps, exps, mod, tokList) <- parseSourceFile fileName

       inscopeNames <- hsFDNamesFromInside mod
       unless (not (name `elem` ((\(x,y) -> x ++ y) inscopeNames)))
        $ error ("the use of the name: " ++ name ++ " is already in scope!")

       let parse = force (parseFile fileContent mod)
       let n = (parseName fileContent mod)
       let extractedDecs = map fst (map extractDecs parse)

       -- b is the boolean value for whether we
       -- are fusing together functions within a where clause or not.
       -- b == True  = not in where clause
       -- b == False = in where clause
       let b = or (map snd (map extractDecs parse))

       -- let extractedDecs' = pad extractedDecs

       newDecl <- doFusing fileName extractedDecs b parse modName mod name

       if b
         then do
          res3 <- applyRefac (addDecls1 newDecl) (Just (inscps, exps, mod, tokList)) fileName

          writeRefactoredFiles True [res3]
          (inscps2, exps2, mod2, tokList2) <- parseSourceFile fileName
          let fusedDecl = declToName newDecl
          let newRefactoredDecls1 = hsDecls mod2
          let newRefactoredDecls2 = definingDecls (map (declToPName [fusedDecl]) newRefactoredDecls1) newRefactoredDecls1 False False
          -- AbstractIO.putStrLn "parsed again"
          sigs <- getSig fileName modName fusedDecl

          res <- applyRefac (addTypes (map (declToPName [fusedDecl]) newRefactoredDecls1) [sigs]) (Just (inscps2, exps2, mod2, tokList2)) fileName
          -- AbstractIO.putStrLn $ show res
          writeRefactoredFiles True [res]
          (inscps5, exps5, mod5, tokList5) <- parseSourceFile fileName
          --(mod',((tokList'',modified),_))<-(doCommenting ( (map (declToPName [fusedDecl]) newRefactoredDecls1))) fileName mod5 tokList5
          --writeRefactoredFiles True [((fileName, True), (tokList'', mod'))]

          AbstractIO.putStrLn "Completed."

         else do
          -- where clause

          -- recurse through each declaration selected.
          -- replace the RHS with a call to the newly
          -- created function
          let selectedDecs = map extractDecs' parse

          res3 <- applyRefac (addDecls2 n newDecl) (Just (inscps, exps, mod, tokList)) fileName

          writeRefactoredFiles True [res3]


          (inscps3, exps3, mod3, tokList3) <- parseSourceFile fileName
          --
          -- AbstractIO.putStrLn $ show newMod

          res4 <- applyRefac (renameCallInSelected selectedDecs name) (Just (inscps3,exps3, mod3, tokList3)) fileName

          writeRefactoredFiles True [res4]

          -- writeRefactoredFiles False [((fileName, m), (newToks, newMod))]

          AbstractIO.putStrLn "Completed."

doFusing fileName extractedDecs b parse  modName mod name
 = do
      (decl, newDecl) <- doFusing' fileName b extractedDecs parse modName mod name

      -- we need to recurse into the where clauses and perform
      -- a fusion if necessary.

      -- x <- fuseWheres decl modName mod ses1
      return decl

fuseExprs :: HsExpP -> HsExpP
fuseExprs exp@(Exp (HsTuple [e1,e2]))
 | (isFst e1 && isSnd e2) && (extractCall e1 == extractCall e2) = extractCall e1
 | otherwise = exp
                 where
                   isFst :: HsExpP -> Bool
                   isFst (Exp (HsInfixApp e1 o e2))
                     = (render.ppi) e1 == "fst"
                   isFst x = False
                   isSnd :: HsExpP -> Bool
                   isSnd (Exp (HsInfixApp e1 o e2))
                     = (render.ppi) e1 == "snd"
                   isSnd x = False

                   extractCall :: HsExpP -> HsExpP
                   extractCall (Exp (HsInfixApp e1 s e2)) = e2
                   extractCall x = x
fuseExprs e = e

fuseWheres d@(Dec (HsFunBind loc0 ms)) modName mod ses1
 = do matches <- lookInMatches ms


      return (Dec (HsFunBind loc0 matches))

       where
        lookInMatches [] = return ([]::[HsMatchP])
        lookInMatches (m@(HsMatch l n p exp@(HsBody exp'@(Exp (HsTuple [e,e1]))) ds):ms)
          = do
             let declNames = filter (/="") (map declToName ds)

             (inscopeNames, inscopeNames2) <- hsFDNamesFromInside d
             let name = ((expAppName e) ++ (expAppName e1))
             let newName = mkNewName name (inscopeNames ++ inscopeNames2) 1
             AbstractIO.putStrLn $ show (expAppName e)
             if (expAppName e) `elem` declNames && (expAppName e1) `elem` declNames
                then do

                   -- find the decl associated with e and e1
                   let decl1 = findDecl (expAppName e) ds
                   let decl2 = findDecl (expAppName e1) ds

                   let extractedDecs = map extractDecs [Right (decl1, False), Right (decl2, False)]

                   -- decl' <- doFusing extractedDecs False [Right decl1, Right decl2] modName ses1 mod newName

                   newExp <- renameFusionInstances exp' newName (map declToPName2 (map extractDecs' [Right (decl1, False), Right (decl2,False)]))


                   rest <- lookInMatches ms

                   -- createTypeSig (retieveTypeSig


                   -- return ((HsMatch l n p (HsBody newExp)
                   return ((HsMatch l n p (HsBody newExp) ds) : rest)

                else do
                   AbstractIO.putStrLn (">" ++ (show e))
                   rest <- lookInMatches ms

                   AbstractIO.putStrLn $ show rest

                   return (m : rest)

        lookInMatches (m:ms)
         =  do
             rest <- lookInMatches ms
             return (m : rest)

        rmDecls :: [HsDeclP] -> (HsDeclP, HsDeclP) -> [HsDeclP]
        rmDecls [] _ = []
        rmDecls (d@(Dec (HsTypeSig _ i _ _)):ds) (d1,d2)
         | declToPName2 d1 `elem` (map pNTtoPN i) = rmDecls ds (d1, d2)
         | declToPName2 d2 `elem` (map pNTtoPN i) = rmDecls ds (d1, d2)
         | otherwise = d : (rmDecls ds (d1, d2))
        rmDecls (d:ds) (d1, d2)
          | d == d1 = rmDecls ds (d1,d2)
          | d == d2 = rmDecls ds (d1,d2)
          | otherwise = d : (rmDecls ds (d1,d2))

        findDecl :: String -> [HsDeclP] -> HsDeclP
        findDecl _ [] = error "error in findDecl!"
        findDecl name (d:ds)
          | (declToName d) == name      = d
          | otherwise                   = findDecl name ds

        expAppName :: HsExpP -> String
        expAppName (Exp (HsApp e1 e2)) = expAppName e1
        expAppName e@(Exp (HsId e1)) = pNtoName (expToPN e)
        expAppName x = ""


doFusing' fileName b extractedDecs parse modName mod name
  = do
       let pairedDecs = pairMatches extractedDecs
       if b
        then do
          converged <- isConvergeArguments fileName modName pairedDecs
          newRhs' <- mapM ( tidyLetClauses mod converged) pairedDecs
          let newDecl = createDecl newRhs' name
          decl' <- renameFusionInstances newDecl name (map declToPName2 (map extractDecs' parse))
          return (decl', newDecl)
        else do
          newRhs' <- mapM ( tidyLetClauses mod True) pairedDecs
          let newDecl = createDecl newRhs' name
          decl' <- renameFusionInstances newDecl name (map declToPName2 (map extractDecs' parse))
          return (decl', newDecl)
-- renameFusionInstances :: (MonadState (([PosToken], Bool), t1) m) => HsDeclP -> String -> PName -> m HsDeclP
renameFusionInstances d _ [] = error "No functions have been selected for fusion!"
renameFusionInstances d n [a,b]
  = do
       dec <- renamePNNoState' a ("fst $ " ++ n)  d
       dec2 <- renamePNNoState' b ("snd $ " ++n)  dec
       return dec2
renameFusionInstances _ _ (x:xs) = error "Only two functions may be fused together!"

force :: Eq a => a -> a
force x = if x == x then x else x

{- tidy up arrangments of let clauses.
   viz:
     f x y = (let ls = x + 1 in ls, let rs = y - 1 in rs)

     should be:

     f x y = let ls = x + 1 ; rs = y - 1 in (ls, rs)

     The idea is that it takes a list of expressions which are
     fused together to form a tuple -- or a list of let declarations
     and a tuple as a body.

     -}

isDupDec :: [String] -> Bool
isDupDec [] = False
isDupDec (x:xs) = (x `elem` xs) || (isDupDec xs)

getDupDec :: [String] -> String
getDupDec [] = ""
getDupDec (x:xs)
 | x `elem` xs = x
 | otherwise   = getDupDec xs


-- tidyLetClauses :: (Monad m, Term t) => t -> Bool -> Fun -> m FunEntity
tidyLetClauses _ _ [] = return Null
tidyLetClauses mod True (m@(Guard p (g@(s,e1,_):gs) ds pnt) : es)
 = do
      let allPats = extractPats' (m:es)
      if all (==(head allPats)) allPats
        then do
           let guards = filterGuards (m:es)
           let guards2 = map (map (\(x,y,z) -> y)) guards
           let decs = map filterLet' guards
           let exps = pairExps (map filterExp' guards)
           let guardExp = filterGuardExp (g:gs)
           -- let (decs, exps) = (filterLet (m:es), (filterExp (m:es)))
           let ds' = filterDec (m:es)
           let dsNames = filter (/="") (map declToName2 ds')

           when (isDupDec dsNames) $ error ( "Please rename " ++ (getDupDec dsNames) ++ " as it conflicts during the merge." )

           when (all (/=(head guards2)) (tail guards2))
            $ error "The guards between the two functions do not match!"


           -- AbstractIO.putStrLn $ show (decs, length decs)

           if length (filter (/=[]) decs) > 0
             then do
                 let returnGuard = createGuardLet guardExp decs exps
                 return (Guard p returnGuard ds' pnt)
             else do
                 let returnGuard = createGuard guardExp exps
                 return (Guard p returnGuard ds' pnt)
                 -- return (Match p gs' ds' pnt)

        else do
           error "The patterns between the functions are not the same set! The patterns must be the same and have the same type."
             where
              pairExps :: [ [HsExpP] ] -> [ (HsExpP, HsExpP) ]
              pairExps [] = []
              pairExps [x::[HsExpP],y::[HsExpP]] = zip x y
              pairExps x = error "Only two functions may be fused together!"

              createGuardLet :: [HsExpP] -> [ [HsDeclP] ] -> [ (HsExpP, HsExpP) ] -> [ (SrcLoc, HsExpP, HsExpP) ]
              createGuardLet [] [] [] = []
              createGuardLet (e:ess) (d:ds) ((x,y):es)
               = (s, e, (Exp (HsLet d (Exp (HsTuple (x:[y])))))) : (createGuardLet ess ds es)


              createGuard :: [HsExpP] -> [ (HsExpP, HsExpP) ] -> [ (SrcLoc, HsExpP, HsExpP) ]
              createGuard [] [] = []
              createGuard (e:ess) ((x,y):es) = (s,e, (Exp (HsTuple (x:[y])))) : (createGuard ess es)


tidyLetClauses mod True (m@(Match p e ds pnt) : es)
  = do
       -- find Let Clauses
       let allPats = extractPats' (m:es)
       if all (==(head allPats)) allPats
         then do

           let (decs, exps) = (filterLet (m:es), filterExp (m:es))
           let ds' = filterDec (m:es)
           let dsNames = (filter (/="") (map declToName2 ds'))
           when (isDupDec dsNames) $ error ( "Please rename " ++ (getDupDec dsNames) ++ " as it conflicts during the merge." )

           if length decs > 0
             then do
                 return (Match p (Exp (HsLet decs (Exp (HsTuple exps)))) ds' pnt)
             else do
                 return (Match p (Exp (HsTuple exps)) ds' pnt)
         else do
           error "The patterns between the functions are not the same set! The patterns must be the same and have the same type."
tidyLetClauses _ False _ = error "The types between the functions to be fused to do match. Please change the types first so that the arguments can converge."
{- tidyLetClauses mod False (m@(Match p e ds pnt) : es)
 = do
      let (decs, exps) = (filterLet (m:es), filterExp (m:es))
      if length decs > 0
        then do
                 let letExp = (Exp (HsLet decs (Exp (HsTuple exps))))
                 (params, exps', ds') <- renameArgs 1 (extractPats (m:es)) letExp ds mod
                 return (Match params exps' ds' pnt)
        else do
                 let letExp = (Exp (HsTuple exps))
                 (params, exps', ds') <- renameArgs 1 (extractPats (m:es)) letExp ds mod
                 return (Match params exps' ds' pnt) -}


extractPats :: Fun -> [ [HsPatP] ]
extractPats [] = []
extractPats ((Match p _ _ _):ms) = p : (extractPats ms)
extractPats ((Guard p _ _ _):ms) = p : (extractPats ms)

extractPats' :: Fun -> [ [String] ]
extractPats' [] = []
extractPats' ((Match p _ _ _):ms) = (map pNtoName (hsPNs p)) : (extractPats' ms)
extractPats' ((Guard p _ _ _):gs) = (map pNtoName (hsPNs p)) : (extractPats' gs)

filterGuardExp :: [(SrcLoc, HsExpP, HsExpP)] -> [HsExpP]
filterGuardExp [] = []
filterGuardExp ((_,e,_):gs) = e : (filterGuardExp gs)

filterGuards :: Fun -> [ [(SrcLoc, HsExpP, HsExpP)] ]
filterGuards [] = []
filterGuards ((Guard _ g _ _):gs) = (rmAllLocs g) : (filterGuards gs)
filterGuards (m:ms) = filterGuards ms

filterDec :: Fun -> [HsDeclP]
filterDec [] = []
filterDec ((Match p e ds pnt):es)= ds ++ (filterDec es)
filterDec ((Guard p g ds pnt):es) = ds ++ (filterDec es)

filterLet' :: [ (SrcLoc, HsExpP, HsExpP) ] -> [HsDeclP]
filterLet' [] = []
filterLet' ((_, _, e@(Exp(HsLet ds _))):gs) = ds ++ (filterLet' gs)
filterLet' (g:gs) = filterLet' gs


filterLet :: Fun  -> [HsDeclP]
filterLet [] = []
filterLet ((Match p e@(Exp (HsLet ds _)) _ pnt) : es) =  ds ++ (filterLet es)
filterLet ((Match p e ds pnt):es)= filterLet es
filterLet ((Guard p gs ds pnt):es) = (findLetInGuard gs) ++ (filterLet es)
                                    where
                                     findLetInGuard [] = []
                                     findLetInGuard ((_, _, (Exp (HsLet ds _))):gs)
                                       = ds ++ (findLetInGuard gs)
                                     findLetInGuard ((_,_, e):gs) = findLetInGuard gs

filterExp' :: [ (SrcLoc, HsExpP, HsExpP) ] -> [HsExpP]
filterExp' [] = []
filterExp' ((_,_, (Exp (HsLet _ e))):es) = e : (filterExp' es)
filterExp' ((_,_, e):es) = e : (filterExp' es)


filterExp :: Fun -> [HsExpP]
filterExp [] = []
filterExp ((Match p (Exp (HsLet _ e)) ds pnt ): es) = e : (filterExp es)
filterExp ((Match p e ds pnt):es) = e : (filterExp es)
filterExp ((Guard p gs ds pnt):es) = (filterExpGuard gs) ++ (filterExp es)
                                      where
                                        filterExpGuard [] = []
                                        filterExpGuard ((_, _, (Exp (HsLet _ e))):gs) = e : (filterExpGuard gs)
                                        filterExpGuard ((_,_, e):gs) =  e : (filterExpGuard gs)

renameArgs index params rhs wheres t
 = do
      -- AbstractIO.putStrLn $ show (map toRelativeLocs (concat params))
      let dups = findDups (concat params)

      (newPats, newExps, newDS) <- doRenaming index dups (concat params) rhs wheres t

      return (newPats, newExps, newDS)

doRenaming :: (Monad m, MonadPlus m, Term t) => Int -> [PName] -> [HsPatP] -> HsExpP -> [HsDeclP] -> t -> m ([HsPatP],HsExpP, [HsDeclP])
doRenaming _ [] a b c _ = return (a,b, c)
doRenaming index (p:ps) pats exps ds t
  = do
       -- names <- mapM (addName t) (concat exps)

       names <- addName t exps

       newPat <- mapM (renamePNNoState p names index) pats

       -- newExp <- mapM (mapListListM (renamePNNoState p (concat names) index)) exps

       newExp <- renamePNNoState p names index exps

       -- newDS <- mapM (mapListListM (renamePNNoState p names index)) ds

       newDS <- renamePNNoState p names index ds

       -- newExp <- mapM (renamePNNoState p name) exps

       rest <- doRenaming (index+1) ps newPat newExp newDS t

       return rest

addName mod e   = do
                   names <- hsVisibleNames e mod
                   return names

-- mapListListM :: [HsExpP] -> m [ [HsExpP] ]
mapListListM f e
  = mapM f e

renamePNNoState oldPN names index t
 = applyTP (full_tdTP (adhocTP idTP rename)) t
     where
       rename (pnt@(PNT pn ty (N (Just (SrcLoc fileName c row col)))))
        | (pn == oldPN) && (srcLoc oldPN == srcLoc pn)
           = return (PNT (replaceNameInPN Nothing pn (mkNewName (pNtoName oldPN) names index )) ty (N (Just (SrcLoc fileName c row col))))
       rename x = return x

renamePNNoState' oldPN name t
 = applyTP (full_tdTP (adhocTP idTP rename)) t
     where
       rename (pnt@(PNT pn ty (N (Just (SrcLoc fileName c row col)))))
        | (pn == oldPN) && (srcLoc oldPN == srcLoc pn)
           = return (PNT (replaceNameInPN Nothing pn name) ty (N (Just (SrcLoc fileName c row col))))
       rename x = return x

renameNameNoState' oldPN name t
 = applyTP (once_tdTP (adhocTP failTP rename)) t
     where
       rename (n::String)
        | n == oldPN
           = return name
       rename x = mzero

findDups :: [HsPatP] -> [PName]
findDups [] = []
findDups (x:xs)  -- do any elements of x occur through out xs?
  | pNtoName (patToPN x) `elem` (map (pNtoName.patToPN) xs) = (patToPN x) : findDups xs
  | otherwise   = findDups xs


doCommenting (x:xs) fileName mod tokList
    =  runStateT (applyTP ((once_tdTP (failTP `adhocTP` (rmInMod (x:xs) )
                                              ))) mod)
                                                         ((tokList,unmodified),fileName)

           where
             --1. The definition to be removed is one of the module's top level declarations.
             rmInMod [] mod = return mod
             rmInMod (p:ps) (mod@(HsModule loc name exps imps ds):: HsModuleP)
                = do ds'<-commentOutTypeSig p ds
                     res2 <- rmInMod ps (HsModule loc name exps imps ds')
                     return res2

addTypes _ [] (_,_,mod) = return mod
addTypes (x:xs) (y:ys) (a,b,mod) = do

                                      mod' <- addTypeSigDecl mod (Just x) ([y], Nothing) True

                                      -- commentOutTypeSig x (y:ys)
                                      res <- addTypes xs ys (a,b,mod')
                                      return mod'


replaceInE :: (Monad m, MonadPlus m) => PNT -> String -> HsExpP -> m HsExpP
replaceInE origName newName e
  = applyTP (once_tdTP (adhocTP idTP rename')) e
     where
        rename' (e'@(Exp (HsId (HsVar x)))::HsExpP)
         | pNTtoName x == pNTtoName origName = return (Exp (HsId (HsVar (nameToPNT newName) )))
         | otherwise = return e'
        rename' e@(Exp (HsApp e1 e2))
         = do res1 <- rename' e1
              res2 <- rename' e2
              return (Exp (HsApp res1 res2))
        rename' e = return e


cleanWhere :: (Monad m, MonadPlus m) => HsDeclP -> [PNT] -> String -> m HsDeclP
cleanWhere (Dec (HsPatBind loc p (HsBody e) ds)) names theName
    = do res2 <- (cleanWhere2 ds names theName)
         return (Dec (HsPatBind loc p (HsBody e) res2))
cleanWhere (Dec (HsFunBind loc (d:dss))) names theName
    = do res2 <- (cleanMatches (d:dss) names theName)
         return (Dec (HsFunBind loc res2))
          where
             cleanMatches :: (Monad m, MonadPlus m) => [HsMatchP] -> [PNT] -> String  -> m [HsMatchP]
             cleanMatches [] _ _ = return []
             cleanMatches ((HsMatch l i1 ps (HsBody e) ds):ms) names theName
                = do res1 <- (cleanWhere2 ds names theName)
                     res2 <- (cleanMatches ms names theName)
                     return ((HsMatch l i1 ps (HsBody e) res1 ): res2)

cleanWhere2 :: (Monad m, MonadPlus m) => [HsDeclP] -> [PNT] -> String -> m [HsDeclP]
cleanWhere2 [] _ _ = return []
cleanWhere2 x [] _ = return x
cleanWhere2 (de@(Dec (HsPatBind loc p (HsBody e) ds)):dss) (name:names) theName
 | pNTtoName (getNameFromExp e) == (pNTtoName name) = do newPats' <- newPats
                                                         newBody <- replaceInE (getNameFromExp e) theName e
                                                         let filteredDecs = filterDecs dss names
                                                         return ((Dec (HsPatBind loc newPats' (HsBody newBody) ds)):filteredDecs)
 | otherwise = do res <- (cleanWhere2 dss names theName)
                  return (de : res )
                                         where
                                          newPats = do res <- findRest dss names
                                                       return (Pat (HsPTuple loc0 (p: res)))
                                          findRest _ [] = return []
                                          findRest [] _ = return []
                                          findRest (de@(Dec (HsPatBind loc p (HsBody e) ds)):dss) (name:names)
                                           | pNTtoName (getNameFromExp e) == (pNTtoName name) = do res <- (findRest dss names)
                                                                                                   return (p : res)
                                           | otherwise = do res <- findRest dss names
                                                            return res
                                          filterDecs [] _ = []
                                          filterDecs (de@(Dec (HsPatBind loc p (HsBody e) ds)):dss) (name:names)
                                            | (getNameFromExp e) `elem` (name:names) = filterDecs dss (name:names)
                                            | otherwise = de : (filterDecs dss (name:names))
getNameFromExp (Exp (HsApp e1 e2))
 = getNameFromExp e1
getNameFromExp e1
 = expToPNT e1

addDecls1 x (_,_,mod) = do
                          mod' <- addDecl mod Nothing ([x], Nothing) True
                          return mod'
addDecls2 n x (_,_,mod) = do
                                 let newDec = convertExpr x
                                 mod' <- doAdding newDec n mod
                                 return mod'
                                  where
                                    doAdding x n mod = applyTP (once_tdTP (failTP `adhocTP` worker)) mod
                                      where
                                        worker (y::HsDeclP)
                                         | y == n = addDecl n Nothing ([x], Nothing) False
                                        worker _ = mzero

convertExpr :: HsDeclP -> HsDeclP
convertExpr (Dec (HsPatBind loc0 pat (HsBody e) ds))
 = (Dec (HsPatBind loc0 pat (HsBody (fuseExprs e)) ds))
convertExpr (Dec (HsFunBind loc0 ms))
 = (Dec (HsFunBind loc0 (newMatches ms)))
     where
       newMatches [] = []
       newMatches (m@(HsMatch loc0 x pats (HsBody e) ds):ms)
             = (HsMatch loc0 x pats (HsBody (fuseExprs e)) ds) : (newMatches ms)
       newMatches (m:ms) = m : (newMatches ms)
convertExpr d = d
renameCallInSelected [d1, d2] name (_,_,mod)
  = applyTP (stop_tdTP (failTP `adhocTP` worker)) mod
          where
              worker d@(Dec (HsPatBind loc0 pat (HsBody e) ds))
                  | d == d1 = do
                                 newDec <- update e (Exp (HsInfixApp (nameToExp "fst") (nameToIdent "$") (nameToExp name))) d
                                 return newDec

                  | d == d2 = do
                                 newDec <- update e (Exp (HsInfixApp (nameToExp "snd") (nameToIdent "$") (nameToExp name))) d
                                 return newDec
              worker d@(Dec (HsFunBind loc0 ms))
                  | d == d1 = do matches <- editMatches ms "fst"
                                 return (Dec (HsFunBind loc0 matches))
                  | d == d2 = do matches <- editMatches ms "snd"
                                 return (Dec (HsFunBind loc0 matches))
                                where
                                  editMatches [] _ = return []
                                  editMatches (m@(HsMatch loc0 _ pats (HsBody e) ds):ms') par
                                     = do
                                          let newPats = map (pNtoExp . patToPN) pats
                                          newMatch <- update e ((Exp (HsInfixApp (nameToExp par) (nameToIdent "$") (createFunc' (nameToExp name ) newPats  )   ))) m
                                          rest <- editMatches ms' par
                                          return (newMatch : rest)
              worker _ = mzero
                                        -- | y == n = addDecl n Nothing ([x], Nothing) False


createDecl :: Fun -> String -> HsDeclP
{-createDecl ((Match [] exps ds _):ms) name
    = (Dec (HsPatBind loc0 (nameToPat name) (HsBody exps) (concat ds))) -}
createDecl (m:ms) name
    = (Dec (HsFunBind loc0 (createMatches (m:ms) )))
       where
        createMatches [] = []
        createMatches ((Guard p guards d _):gs)
          =
             (HsMatch loc0 (nameToPNT name) p (HsGuard guards) d) : (createMatches gs)
        createMatches ((Match p e d _):ms)
          =
             (HsMatch loc0 (nameToPNT name) p (HsBody e) d) : (createMatches ms)

extractDecs :: Either String (HsDeclP, Bool) -> (Fun, Bool)
extractDecs dec
  = do
       case dec of
         Left errMsg -> error errMsg
         Right (decl, b) -> extractDecl (decl, b)

extractDecs' :: Either String (HsDeclP, Bool) -> HsDeclP
extractDecs' dec
  = do
       case dec of
         Left errMsg -> error errMsg
         Right (decl,_) -> decl


-- pad :: [ [a] ] -> [ [a] ]
count list = maximum ( map length list )

pad list = map (pad' (count list)) list
             where
               pad' count entry = entry ++ (replicate count (head entry))

{- converge arguments attemps to converge the arguments of the pairs where ever possible.
   The selected functions must have the same set of patterns, if not then
   convergeArguments returns an error. Otherwise, the types of each function are taken,
   if the types match then only use the first set of arguments. Otherwise, do nothing.
   It is sensible to let the user instantiate patterns so that a more general instance converges
   with a more specific type. -}

{-
data FunEntity = Match [HsPatP] HsExpP [HsDeclP] PNT | Null
                   deriving (Eq, Show)

type Fun = [ FunEntity ]

-- we can "pair" an arbitrary number of matches together so
-- we can't use a tuple. We don't know the number of
-- function to fuse!
type PairFun = [ Fun ] -}

-- convergeArguments :: (Monad m) => String -> GHC.Session -> PairFun -> m Bool
isConvergeArguments _ _ [] = return False
isConvergeArguments fileName modName (ent:ents)
 = do -- entType <- typeOf modName ses ent
      entsType <-typeOf fileName modName ent

      AbstractIO.putStrLn $ show entsType
      -- AbstractIO.putStrLn $ show (map hsPNs (settleTypes entsType))
      --let res = myAll (map pNtoName (map hsPNs (settleTypes entsType)))
      let res = myAll entsType
      return res
        where
          -- myAll :: Eq a => [a] -> Bool
          myAll :: [ [String] ] -> Bool
          myAll [] = False
          myAll (l:ls) = all (==l) ls

settleType :: HsDeclP -> HsDeclP
settleType (Dec (HsTypeSig x _ y types))
    = (Dec (HsTypeSig x [] y types))


typeOf :: (Monad m) => String -> String -> [FunEntity] -> m [ [String] ]
typeOf fileName modName [] = return []
typeOf fileName modName (m:ms)
  = do
       sig <- getSigOmitLast modName (nameFromMatch m) fileName
       let sig' = hsPNs (settleType sig)
       let sig'' = map pNtoName sig'

       sigs <- typeOf fileName modName ms
       return (sig'' : sigs)

nameFromMatch :: FunEntity -> String
nameFromMatch  (Match _ _ _ pnt) = pNTtoName pnt
nameFromMatch Null = ""


pairMatches :: [ Fun ] -> PairFun
pairMatches [] = []
pairMatches [ e] = [ e ]
pairMatches (e:es)
  = ((take 1 e) ++ (concat (map (take 1) es))) : (pairMatches (filter (/=[]) (((gtail "e" e):(map (drop 1) es)))))



extractDecl :: (HsDeclP, Bool) -> (Fun, Bool)
-- extractDecl :: HsDeclP -> ( [[HsPatP]], [HsExpP], [HsDeclP] , PNT)
extractDecl (d@(Dec (HsPatBind loc p (HsBody e) ds)),b) = ([Match [] e ds (patToPNT p)],b)
extractDecl ((Dec (HsFunBind loc (d:dss ))),b) = (extractMatches (d:dss),b)
                                                  where
                                                   extractMatches [] = []
                                                   extractMatches ((HsMatch l i1 ps (HsBody e) ds):ms)
                                                                = (Match ps e ds i1) : extractMatches ms
                                                   extractMatches ((HsMatch l i1 ps (HsGuard g) ds):ms)
                                                                = (Guard ps g ds i1) : extractMatches ms
                                                   {-
                                                                          =  ((ps : ps2) , (e : e2) , (ds ++ ds2), i1)
                                                                              where
                                                                                (ps2, e2, ds2, _) = extractMatches ms    -}


-- parseFile :: String -> HsModuleP -> [Either String (HsDeclP, Bool)]
parseName [] _ = error "error in parseName!"
parseName ('>':xs) mod =  checkCursor' fileName (read row) (read col) mod
                            where
                             (fileName, rest) = parseFileName xs
                             (row, rest2) = parseRow rest
                             (col, rest3) = parseCol rest2

parseFile :: String -> HsModuleP -> [Either String (HsDeclP, Bool)]
parseFile [] _ = []
parseFile ('>':xs) mod =  (checkCursor fileName (read row) (read col) mod) : (parseFile (tail rest3) mod)
                            where
                             (fileName, rest) = parseFileName xs
                             (row, rest2) = parseRow rest
                             (col, rest3) = parseCol rest2

parseFileName :: String -> (String, String)
parseFileName [] = ([], [])
parseFileName xs = ((takeWhile (/= '<') xs), (dropWhile (/= '<') xs))

parseRow :: String -> (String, String)
parseRow [] = ([], [])
parseRow xs = ((takeWhile (/= '%') (tail xs')), dropWhile (/= '%') (tail xs'))
                where
                 xs' = dropWhile (/= '%') xs

parseCol :: String -> (String, String)
parseCol [] = ([], [])
parseCol xs = ((takeWhile (/= '&') (tail xs') ), dropWhile (/= '&') (tail xs') )
                where
                 xs' = dropWhile (/= '&') xs
--check whether the cursor points to the beginning of the datatype declaration
--taken from RefacADT.hs
checkCursor :: String -> Int -> Int -> HsModuleP -> Either String (HsDeclP, Bool)
checkCursor fileName row col mod
 = case locToPName of
     (Nothing, _) -> Left ("Invalid cursor position. Please place cursor at the beginning of the definition!")
     (Just decl, b) -> Right (decl, b)
    where
        locToPName
         = case res of
             Nothing -> (find (definesPNT (locToPNT fileName (row, col) mod)) (hsDecls mod), True)
             _ -> (res, False)
        res =  find (defines (locToPN fileName (row, col) mod)) (concat (map hsDecls (hsModDecls mod)))

        definesPNT pnt d@(Dec (HsPatBind loc p e ds))
         = findPNT pnt d
        definesPNT pnt d@(Dec (HsFunBind loc ms))
         = findPNT pnt d
        definesPNT _ _ = False

checkCursor' :: String -> Int -> Int -> HsModuleP -> HsDeclP
checkCursor' fileName row col mod
 = case locToPName of
     Nothing -> error "Invalid cursor position. Please place cursor at the beginning of the definition!"
     Just decl -> decl
    where
        locToPName = find (definesPNT (locToPNT fileName (row, col) mod)) (hsDecls mod)

        definesPNT pnt d@(Dec (HsPatBind loc p e ds))
         = findPNT pnt d
        definesPNT pnt d@(Dec (HsFunBind loc ms))
         = findPNT pnt d
        definesPNT _ _ = False

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
--find the definition name whose sub-expression has been selected, and the selected sub-expression.
findDefNameAndExp toks beginPos endPos t
  = fromMaybe (defaultPNT, defaultExp) (applyTU (once_tdTU (failTU `adhocTU` inMatch
                                                                   `adhocTU` inPat)) t)  --CAN NOT USE 'once_tdTU' here.

     where  --The selected sub-expression is in the rhs of a match
           inMatch (match@(HsMatch loc1  pnt pats rhs ds)::HsMatchP)
             | locToExp2 beginPos endPos toks rhs /= defaultExp
             = Just (pnt, locToExp2 beginPos endPos toks rhs)
           inMatch _ = Nothing

           --The selected sub-expression is in the rhs of a pattern-binding
           inPat (pat@(Dec (HsPatBind loc1 ps rhs ds))::HsDeclP)
             | locToExp2 beginPos endPos toks rhs /= defaultExp
             = if isSimplePatBind pat
                then Just (patToPNT ps, locToExp2 beginPos endPos toks rhs)
                else error "A complex pattern binding can not be generalised!"
           inPat _ = Nothing
