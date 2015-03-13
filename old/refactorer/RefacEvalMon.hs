module RefacEvalMon (refacEvalMon) where
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
import LocalSettings(evalFilePath)


refacEvalMon args =
  do let fileName = args!!0
         beginRow = read (args!!1)::Int
         beginCol = read (args!!2)::Int
         endRow   = read (args!!3)::Int
         endCol   = read (args!!4)::Int
     modName <- fileNameToModName fileName

     (inscps, exps, mod, tokList) <- parseSourceFile fileName
     let pnt       = locToPNT fileName (beginRow, beginCol) mod
     unless (not (isFunPNT pnt mod)) $ error "Cannot spark a function! Please select a pattern binding instead."

     unless ( isHidden ["rpar", "runEval"] (concat  (findImportsHiddenLists mod)) == [] )
          $ error "rpar and/or runEval are explicitly hidden. Please unhide and try again."


     let (thePar, theRunEval) = checkForQualifiers ("rpar", "runEval") inscps

     -- check if we have an active eval monad or not...
     -- read from the cache...

     fileContent <- AbstractIO.readFile evalFilePath

     -- AbstractIO.putStrLn $ show mod

     AbstractIO.putStrLn ("Grabbing monad from " ++ evalFilePath)

     if (fileContent == [])
       then do AbstractIO.putStrLn "No Active Eval Monad. Creating one..."

               ((_, m), (newToks, newMod)) <- applyRefac (doIntroduce pnt thePar theRunEval) (Just (inscps, exps, mod, tokList)) fileName

               writeRefactoredFiles False [((fileName, m), (newToks, newMod))]

               AbstractIO.putStrLn "refacEvalMon completed."

       else do
               AbstractIO.putStrLn "Using activated Eval Monad."

               let thePat = read (fileContent) :: HsPatP

               AbstractIO.putStrLn ("thePat: " ++ (show thePat))

               ((_, m), (newToks, newMod)) <- applyRefac (doIntroduceWithActivePat pnt thePat thePar) (Just (inscps, exps, mod, tokList)) fileName

               writeRefactoredFiles False [((fileName, m), (newToks, newMod))]

               AbstractIO.putStrLn "refacEvalMon completed."


checkForQualifiers (r,ru) inscps
  = (ck1 r inscps, ck1 ru inscps)
 where
      ck1 r i
       | isInScopeAndUnqualified r i = r
       | length res == 0 = r
       | length res > 1 = error (r ++ " is qualified more than once. " ++ r ++ " must only be qualified once or not at all to proceed.")
       | otherwise      = if res /= [] then (modNameToStr (head res)) ++"."++ r else r
          where res = hsQualifier2 (nameToPNT r) i

isHidden [] ys = []
isHidden (x:xs) ys
  | elem x ys = x : isHidden xs ys
  | otherwise = isHidden xs ys

findImportsHiddenLists
  = applyTU (full_tdTU (constTU [] `adhocTU` inImport))
    where
      inImport (HsImportDecl loc modName qual _ (Just (True, h))::HsImportDeclP) = return ((map (\(Var x) -> (pNTtoName x))) h)
      inImport _ = return []


doIntroduce pnt thePar theRunEval (_,_,t)
 = do
     mod <- doIntroduce' pnt thePar theRunEval t
     if mod == t
       then return t
       else do
               mod' <- addTheImport [thePar, theRunEval] mod
               return mod'

doIntroduceWithActivePat pnt thePat thePar (_,_,t)
  = do
        mod <- doIntroduceWPat pnt thePat thePar t
        return mod

addTheImport ss mod
  = addImport "" (strToModName "Control.Parallel.Strategies") (map nameToPN ss) mod


doIntroduceWPat pnt thePat thePar t
  = applyTP (once_buTP (failTP `adhocTP` inCase
                               `adhocTP` inExp
                               `adhocTP` inPat
                               `adhocTP` inMatch
                               `adhocTP` inModule ) `choiceTP` failure) t
      where
         inExp l@(Exp (HsLet decls e)::HsExpP)
          | isDeclaredIn (pNTtoPN pnt) l
             = do
                  (f,d) <- hsFDNamesFromInside l
                  let newName = mkNewName (pNTtoName pnt) (f++d) 2

                  l' <- replacePNTs l pnt (nameToPNT newName)

                  let thePat2 = findPat thePat decls
                  if thePat2 == Nothing
                     then mzero
                     else do let newPat = augmentPat (nameToPNT newName) (fromJust thePat2)

                             l'' <- update (fromJust thePat2) newPat l'

                             return l''



         inExp l@(Exp (HsListComp stmts)::HsExpP)
          | (pNTtoPN pnt) `elem` (findIn stmts)
               = do
                    (f,d) <- hsFDNamesFromInside l
                    let newName = mkNewName (pNTtoName pnt) (f++d) 2

                    l' <- newStmts l pnt (nameToPNT newName)

--                    l' <- replacePNTs l pnt (nameToPNT newName)

                    let theLast = findLast stmts
                        thePat2 = findPat thePat theLast
                    if thePat2 == Nothing
                         then mzero
                         else do let newPat = augmentPat (nameToPNT newName) (fromJust thePat2)

                                 l'' <- update (fromJust thePat2) newPat l'
                                 return l''

           where
              newStmts (Exp (HsListComp s)) x y = do res <- newStmts' s x y
                                                     return (Exp (HsListComp res))

              newStmts' (HsLast e) pnt newName  = do l' <- replacePNTs e pnt newName
                                                     return (HsLast l')
              newStmts' (HsGenerator a b c s) x y = do  res <- newStmts' s x y
                                                        return (HsGenerator a b c res)



 {-     findLast :: HsStmtP -> [HsDeclP]
         findLast (HsGenerator l p2 e s)  = (findLast s)
         findLast (HsQualifier e s)       = (findLast s)
         findLast (HsLetStmt ds s )       = (findLast s)
         findLast (HsLast (Exp (HsLet ds e))) = ds
         findLast _ = []
-}


         inExp _ = mzero


         inCase (alt@(HsAlt loc p rhs ds)::HsAltP)
          | isDeclaredIn (pNTtoPN pnt)  alt
            = do (f,d) <- hsFDNamesFromInside alt
                 let newName = mkNewName (pNTtoName pnt) (f++d) 2

                 alt'@(HsAlt loc' p' rhs' ds') <- replacePNTs alt pnt (nameToPNT newName)


                 let thePat2 = findPat thePat ds
                 if thePat2 == Nothing
                     then mzero
                     else do let newPat = augmentPat (nameToPNT newName) (fromJust thePat2)

                             -- we don't have  an binding to add new decl after, so just plonk into Where clause of case...

                             alt'' <- update (fromJust thePat2) newPat alt'
                             return alt''
         inCase _ = mzero


         inModule (mod::HsModuleP)
          | isDeclaredIn (pNTtoPN pnt) mod
            = do
              (f,d) <- hsFDNamesFromInside mod
              let newName = mkNewName (pNTtoName pnt) (f++d) 2

              mod' <- replacePNTs mod pnt (nameToPNT newName)


              let thePat2 = findPat thePat (hsDecls mod)

              if thePat2 == Nothing
                     then mzero
                     else do let newPat = augmentPat (nameToPNT newName) (fromJust thePat2)

                             mod'' <- update (fromJust thePat2) newPat mod'
                             return mod''
         inModule _ = mzero

         inPat  (pat@(Dec (HsPatBind l p rhs ds))::HsDeclP)
           | (pNTtoPN pnt) `elem` (toPat ds)
          && thePat `myElem` (hsDecls rhs)
           = do  (f,d) <- hsFDNamesFromInside pat
                 let newName = mkNewName (pNTtoName pnt) (f++d) 2

                 pat' <- replacePNTs pat pnt (nameToPNT newName)

                 let thePat2 = findPat thePat (hsDecls rhs)

                 if thePat2 == Nothing
                    then mzero
                    else do let newPat = augmentPat (nameToPNT newName) (fromJust thePat2)

                            pat'' <- update (fromJust thePat2) newPat pat'
                            return pat''

         inPat (pat@(Dec (HsPatBind l p rhs ds))::HsDeclP)
           | thePat `myElem` ds
           && isDeclaredIn (pNTtoPN pnt) pat
               = do  (f,d) <- hsFDNamesFromInside pat
                     let newName = mkNewName (pNTtoName pnt) (f++d) 2

                     pat' <- replacePNTs pat pnt (nameToPNT newName)

                     let thePat2 = findPat thePat ds

                     if thePat2 == Nothing
                        then mzero
                        else do let newPat = augmentPat (nameToPNT newName) (fromJust thePat2)

                                pat'' <- update (fromJust thePat2) newPat pat'
                                return pat''
         inPat _ = mzero


         -- could be the case that run eval in an inner scope on the RHS, but
         -- selected runEval is in the where clause, scoping over the RHS
         inMatch (match@(HsMatch l name pats rhs ds)::HsMatchP)
          -- = error $ show ((pNTtoPN pnt), toPat ds)
           |  (pNTtoPN pnt) `elem` (toPat ds)
           && thePat `myElem` (hsDecls rhs)
            = do (f,d) <- hsFDNamesFromInside match
                 let newName = mkNewName (pNTtoName pnt) (f++d) 2
                 match' <- replacePNTs match pnt (nameToPNT newName)
                 let pat' = findPat thePat (hsDecls rhs)
                 if pat' == Nothing
                    then mzero
                    else do let newPat = augmentPat (nameToPNT newName) (fromJust pat')
                            match'' <- update (fromJust pat') newPat match'
                            return match''


         inMatch (match@(HsMatch l name pats rhs ds)::HsMatchP)
           |  thePat `myElem` ds     -- = error (show match)
           && isDeclaredIn (pNTtoPN pnt) match
               = do (f,d) <- hsFDNamesFromInside match
                    let newName = mkNewName (pNTtoName pnt) (f++d) 2
                    match' <- replacePNTs match pnt (nameToPNT newName)
                    let pat' = findPat thePat ds
                    if pat' == Nothing
                     then mzero
                     else do -- modify the pattern, - add the new binding as a tuple!
                           let newPat = augmentPat (nameToPNT newName) (fromJust pat')
                           match'' <- update (fromJust pat') newPat match'
                           return match''

         inMatch s = mzero




         failure=idTP `adhocTP` mod
                 where mod (m::HsModuleP) = error "Cannot find the active eval monad!"


         augmentPat pnt thePat@(Dec (HsPatBind l p rhs ds))
           = Dec (HsPatBind l newPat newRHS ds)
                where newPat = addToPat pnt p
                      newRHS = addToRHS pnt rhs

         toPat :: [HsDeclP] -> [PName]
         -- toPat x = error $ show x
         toPat [] = []
         toPat ((Dec (HsPatBind loc p rhs ds)):xs) = patToPN p : toPat xs
         toPat (_:xs) = toPat xs


         findLast :: HsStmtP -> [HsDeclP]
         findLast (HsGenerator l p2 e s)  = (findLast s)
         findLast (HsQualifier e s)       = (findLast s)
         findLast (HsLetStmt ds s )       = (findLast s)
         findLast (HsLast (Exp (HsLet ds e))) = ds
         findLast _ = []

         findIn :: HsStmtP -> [PName]
         findIn (HsGenerator l p2 e s)  = res ++ findIn s
                                            where res =  fromJust (do (pf,pd) <-hsFreeAndDeclaredPNs p2
                                                                      Just pd)

         findIn (HsQualifier e s)       = (findIn s)
         -- findIn (HsLetStmt ds s )       = ds ++ findIn s
         findIn (HsLast e) = fromJust (do (pf, pd) <- hsFreeAndDeclaredPNs e
                                          Just pd)
         findIn _ = []

         -- addToRHS p e = error (show e)

         addToRHS p (HsBody (Exp (HsInfixApp e1 o (Exp (HsDo s)))))
           = HsBody (Exp (HsInfixApp e1 o (Exp (HsDo (addToStatements p s)))))

         addToRHS p (HsBody (Exp (HsApp e1 (Exp (HsParen (Exp (HsDo s)))))))
           = HsBody (Exp (HsApp e1 (Exp (HsParen (Exp (HsDo (addToStatements p s)))))))

         addToRHS p (HsBody (Exp (HsApp e1 (Exp (HsDo s)))))
           = HsBody (Exp (HsApp e1 (Exp (HsDo (addToStatements p s)))))

         addToRHS p (HsBody (Exp e)) = error "Active Eval Monad must be in do notation!"

         addToRHS p (HsGuard gs) = error "addToRHS guards"

         addToStatements p (HsGenerator l p2 e s) = HsGenerator l p2 e (addToStatements p s)
         addToStatements p (HsQualifier e s)     = HsQualifier e (addToStatements p s)
         addToStatements p (HsLetStmt ds s )     = HsLetStmt ds  (addToStatements p s)
         addToStatements p (HsLast e)
           = (HsGenerator loc0 (nameToPat $ pNTtoName p) (Exp (HsApp {-(nameToExp "rpar")-} (nameToExp thePar) (nameToExp (pNTtoName pnt))))
                                                         (HsLast (updateTuple p e)))

         updateTuple p (Exp (HsApp e1 (Exp (HsTuple es)))) = Exp (HsApp e1 (Exp (HsTuple (es ++ [ pNtoExp (pNTtoPN p)] ))))

         updateTuple p (Exp (HsApp e1 e@(Exp (HsId i)))) = Exp (HsApp e1 (Exp (HsTuple [e,  pNtoExp (pNTtoPN p)])))

         updateTuple p _ = error "Eval Monad must return a tuple or variable expression!"

-- HsGenerator loc0 (pNtoPat $ nameToPN newPat) (Exp (HsApp (nameToExp thePar) (nameToExp origPat))) (HsLast (Exp (HsApp (nameToExp "return") (nameToExp newPat))))





         addToPat p a@(Pat (HsPId i)) = Pat (HsPTuple loc0 [a, nameToPat (pNTtoName p)])
         addToPat p (Pat (HsPTuple s as)) = Pat (HsPTuple s (as ++ [nameToPat (pNTtoName p)]))
         addToPat p _ = error "Active Eval Monad must be a tuple pattern binding or variable pattern binding!"


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

doIntroduce' pnt thePar theRunEval t
  = applyTP (once_buTP (failTP -- `adhocTP` inLambda
                               -- `adhocTP` inListComp
                               -- `adhocTP` inCase
                               -- `adhocTP` inDo
                               -- `adhocTP` inLet
                               -- `adhocTP` inPat
                               -- `adhocTP` inMatch
                               `adhocTP` inModule
                               `adhocTP` inMatch
                               `adhocTP` inPat
                               `adhocTP` inExp
                               -- `adhocTP` inLet
                               -- `adhocTP` inDo
                               `adhocTP` inCase
                               ) `choiceTP` failure) t
     where
       inMatch (match@(HsMatch l name pats rhs ds)::HsMatchP)
         | isDeclaredIn (pNTtoPN pnt) match
              = do (f,d) <- hsFDNamesFromInside match
                   let newName = mkNewName (pNTtoName pnt) (f++d) 2

                   match' <- replacePNTs match pnt (nameToPNT newName)

                   -- let match' = HsMatch l name pats rhs' ds

                   -- add the runEval declaration ...
                   match'' <- addDecl match' Nothing ([newDecl newName (pNTtoName pnt)], Nothing) False

                   -- substitute the RHS for occurrences of it...
                   return match''
       inMatch _ = mzero

       inPat (pat@(Dec (HsPatBind l p rhs ds))::HsDeclP)
         | isDeclaredIn (pNTtoPN pnt)  pat
             = do  (f,d) <- hsFDNamesFromInside pat
                   let newName = mkNewName (pNTtoName pnt) (f++d) 2

                   pat' <- replacePNTs pat pnt (nameToPNT newName)

                   -- let pat' = Dec (HsPatBind l p rhs' ds)

                   pat'' <- addDecl pat' Nothing ([newDecl newName (pNTtoName pnt)], Nothing) False
                   return pat''
       inPat _ = mzero

       inExp (lam@(Exp (HsLambda p e))::HsExpP)
         | isDeclaredIn (pNTtoPN pnt) e = error "Cannot extract lambda binding! Please lift the binding to a let/where clause first."
       inExp lComp@(Exp (HsListComp stms)::HsExpP)
         | isDeclaredIn (pNTtoPN pnt) stms
              = do -- add the definition as a let (or a where...?)

                 (f,d) <- hsFDNamesFromInside lComp
                 let newName = mkNewName (pNTtoName pnt) (f++d) 2

                 l' <- replacePNTs lComp pnt (nameToPNT newName)

                 let newStmts = addToLast stms pnt newName
                 -- error $ show newStmts
                 l'' <- update l' (Exp (HsListComp newStmts)) l'
                 return l''

       inExp doSt@(Exp (HsDo sts)::HsExpP)
         | isDeclaredIn (pNTtoPN pnt) sts = error "Cannot parallelise monadic expressions, please de-monadify first."
       inExp l@(Exp (HsLet decls e)::HsExpP)
         | isDeclaredIn (pNTtoPN pnt) l
             = do
                  (f,d) <- hsFDNamesFromInside l
                  let newName = mkNewName (pNTtoName pnt) (f++d) 2

                  l' <- replacePNTs l pnt (nameToPNT newName)

                  l'' <- addDecl l' {-(Just (pNTtoPN pnt))-} Nothing ([newDecl newName (pNTtoName pnt)], Nothing) False
                  return l''
       inExp _ = mzero

       inLambda (lam@(Exp (HsLambda p e))::HsExpP)
         | isDeclaredIn (pNTtoPN pnt) e = error "Cannot extract lambda binding! Please lift the binding to a let/where clause first."
       inLambda _ = error "here" -- mzero

       inCase (alt@(HsAlt loc p rhs ds)::HsAltP)
         | isDeclaredIn (pNTtoPN pnt)  alt
            = do (f,d) <- hsFDNamesFromInside alt
                 let newName = mkNewName (pNTtoName pnt) (f++d) 2

                 alt'@(HsAlt loc' p' rhs' ds') <- replacePNTs alt pnt (nameToPNT newName)


                 -- we don't have  an binding to add new decl after, so just plonk into Where clause of case...
                 alt'' <- addDecl alt' Nothing ([newDecl newName (pNTtoName pnt)], Nothing) False
                 return alt''


       inCase _ = mzero

       -- inDo doSt@(Exp (HsDo sts)::HsExpP)
       --  | isDeclaredIn (pNTtoPN pnt) sts = error "Cannot parallelise monadic expressions, please de-monadify first."
       -- inDo _ = mzero

--       inLet l@(Exp (HsLet decls e)::HsExpP)
  --       | isDeclaredIn (pNTtoPN pnt) l
    --         = do
      --            (f,d) <- hsFDNamesFromInside l
        --          let newName = mkNewName (pNTtoName pnt) (f++d) 2

          --        l' <- replacePNTs l pnt (nameToPNT newName)

          --        l'' <- addDecl l' {-(Just (pNTtoPN pnt))-} Nothing ([newDecl newName (pNTtoName pnt)], Nothing) False
          --        return l''

       -- inLet _ = mzero

       -- inListComp lComp@(Exp (HsListComp stms)::HsExpP)
       --  = error $ show (pnt, lComp)
    --     | isDeclaredIn (pNTtoPN pnt) stms = error "Cannot parallelise binding in a list comprehension. Please extract binding to a let/where first."
       -- inListComp _ = mzero


       inModule (mod::HsModuleP)
         | isDeclaredIn (pNTtoPN pnt) mod
           = do
              (f,d) <- hsFDNamesFromInside mod
              let newName = mkNewName (pNTtoName pnt) (f++d) 2

              mod' <- replacePNTs mod pnt (nameToPNT newName)

              mod'' <- addDecl mod' Nothing ([newDecl newName (pNTtoName pnt)], Nothing) False

              return mod''
       inModule _ = mzero

       failure=idTP `adhocTP` mod
                 where mod (m::HsModuleP) = error "Cannot find the declaration for the highlighted expression!"


       newDecl newPat origPat
         = Dec (HsPatBind loc0 (pNtoPat $ nameToPN newPat) (HsBody e) [])
          where
            e = (Exp (HsApp (nameToExp theRunEval) (Exp (HsDo sts))))
            sts = HsGenerator loc0 (pNtoPat $ nameToPN newPat) (Exp (HsApp (nameToExp thePar) (nameToExp origPat))) (HsLast (Exp (HsApp (nameToExp "return") (nameToExp newPat))))

       addToLast :: HsStmtP -> PNT -> String -> HsStmtP
       addToLast (HsGenerator l p2 e s) pnt n = HsGenerator l p2 e (addToLast s pnt n)
       addToLast (HsQualifier e s) pnt n      = HsQualifier e (addToLast s pnt n)
       addToLast (HsLetStmt ds s ) pnt n      = HsLetStmt ds  (addToLast s pnt n)
       addToLast (HsLast e) pnt newName
         = (HsLast (Exp (HsLet ([newDecl newName (pNTtoName pnt)]) e)))


replacePNTs t oldName newName
  = applyTP (full_tdTP (idTP `adhocTP` inPNT)) t
     where
      inPNT (p::PNT)
        | (not (sameOccurrence p oldName)) && definesPNT p oldName = update p newName p
      inPNT p = return p
