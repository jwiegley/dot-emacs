module RefacRedunDec (convertPatsToPn,
                      convertToPat,
                      refacRedunDec,
                      removeRedun,
                      removeRedunWhere,
                      removeRedunWhere2,
                      doRemovingWhere, doRemoving1, doRefac) where


import AbstractIO
import Data.Maybe
import Data.List
import RefacUtils
import RefacLocUtils

data Patt = Match HsMatchP | MyPat HsDeclP | Def [Char]

refacRedunDec args
  = do let fileName   = args!!0
           beginRow   = read (args!!1)::Int
           beginCol   = read (args!!2)::Int
           endRow     = read (args!!3)::Int
           endCol     = read (args!!4)::Int
       AbstractIO.putStrLn "refacRedunDec"

       -- Parse the input file.
       modInfo@(inscps, exps, mod, tokList) <- parseSourceFile fileName

       -- Find the function that's been highlighted as the refactree

       let (loc, pnt, pats, exp, wh, p)
             = findDefNameAndExp tokList
                                 (beginRow, beginCol)
                                 (endRow, endCol)
                                 mod


       (wh', newExp) <- removeRedunCase exp wh
       (wh'', newExp') <- doRefac wh' newExp

       -- (mod',((tokList',modified),_))<-doRemovingWhere fileName mod tokList exp newExp wh'

       ((_,_), (tokList', mod')) <- applyRefac (doRemovingWhere exp newExp' wh'') (Just (inscps, exps, mod, tokList)) fileName


       ((_,m), (tokList'', mod'')) <- applyRefac (doRemoving1 exp newExp' wh'') (Just (inscps, exps, mod', tokList')) fileName


       writeRefactoredFiles False [((fileName, True), (tokList'', mod''))]

    --   error (show mod')
       AbstractIO.putStrLn "Completed.\n"

doRefac wh exp = do
                 (decls, newExp) <- removeRedun wh exp
                 (newWhere) <- removeRedunWhere wh newExp
                 return (newWhere, newExp)

convertToPat [] _ = []
convertToPat _ [] = []
convertToPat (pat@(Pat (HsPId (HsVar (PNT (PN x y) Value s)))):ps) ((PN v z):xs)
      | x == v && y == z = pat : (convertToPat ps xs)
      | otherwise        = convertToPat ps ((PN v z):xs)


convertPatsToPn [] = []
convertPatsToPn ((Pat (HsPId (HsVar (PNT (PN x y)Value s )))):ps)
                           = (PN x y): (convertPatsToPn ps)
convertPatsToPn _ = []


--removeRedun :: [HsDeclP] -> HsExpP -> m ([HsDeclP], HsExpP)

removeRedunCase (Exp(HsParen e)) wh
                = do
                     res <- removeRedunCase e wh
                     return res
removeRedunCase (Exp(HsCase e alts)) wh
                = do
                     newAlts <- checkAlts alts
                     return (wh, (Exp (HsCase e newAlts)))
                        where
                           checkAlts [] = do
                                             return []
                           checkAlts ((HsAlt s p1 (HsBody e) ds):xs)
                              = do
                                   decls <- removeRedunWhere ds e
                                   res <- checkAlts xs
                                   return ((HsAlt s p1 (HsBody e) decls) : res)

removeRedunCase (exp@e) wh  = do
                               return (wh, e)

removeRedun wh (Exp (HsParen e))
   = do
        (wh', newExp) <- removeRedun wh e
        return (wh', (Exp (HsParen newExp)))

removeRedun wh (Exp (HsInfixApp e1 o e2))
 = do
      (wh'1, newExp1) <- removeRedun wh e1
      (wh'2, newExp2) <- removeRedun wh e2

      return ( nub ( wh'2 ++ wh), (Exp (HsInfixApp newExp1 o newExp2)))

removeRedun wh (Exp(HsLet ds e)) = do
                                   (_, newE) <- removeRedun wh e
                                   (free, dec) <- hsFreeAndDeclaredPNs newE
                                   let decls = checkFree free ds
                                   let decls' = checkFree free wh
                                   newWhere <- checkWhere wh decls
                                   moreDecls <- checkRestDecls decls' wh
                                   if decls /= []
                                      then do
                                        return ((nub (moreDecls++(decls'++newWhere))), (Exp(HsLet decls newE)))
                                      else do
                                        return ((nub (moreDecls++(decls'++newWhere))), newE)
                                      where
                                         checkWhere [] _ = do return wh
                                         checkWhere wh [] = do return wh
                                         checkWhere wh ((Dec(HsPatBind _ _ (HsBody e)_)):xs)
                                                      = do
                                                           (free, dec) <- hsFreeAndDeclaredPNs e
                                                           let decls = checkFree free wh
                                                           newDecls <- checkWhere decls xs
                                                           moreDecls <- checkRestDecls newDecls wh
                                                           return (nub (moreDecls ++ newDecls))
removeRedun wh exp@(Exp (HsLambda (p:ps) e))
      = do
           (free, dec) <- hsFreeAndDeclaredPNs e
           -- error $ show (free, (p:ps))
           let decls = myCheckFree e (p:ps)
           let decls' = checkFree free wh
           -- newWhere <- checkWhere wh [(Exp (HsLambda decls e))]
           moreDecls <- checkRestDecls decls' wh
           return ((nub (moreDecls ++ (decls'))), (Exp (HsLambda decls e)))
            where
              myCheckFree e list = checkSin e list
                                       where
                                        checkSin :: HsExpP -> [HsPatP] -> [HsPatP]
                                        checkSin e [] = []
                                        checkSin e (x:xs)
                                          | findPN' (patToPN x) e = x : checkSin e xs
                                          | otherwise   = checkSin e xs

              checkWhere [] _ = do return wh
              checkWhere wh [] = do return wh
              checkWhere wh ((Dec(HsPatBind _ _ (HsBody e)_)):xs)
                                   = do
                                       (free, dec) <- hsFreeAndDeclaredPNs e
                                       let decls = checkFree free wh
                                       newDecls <- checkWhere decls xs
                                       moreDecls <- checkRestDecls newDecls wh
                                       return (nub (moreDecls ++ newDecls))

removeRedun wh (exp@(_)) = do return (wh, exp)

removeRedunWhere wh (exp@(_)) = do
                      (free, dec) <- hsFreeAndDeclaredPNs exp
                      let decls = checkFree free wh
                      -- check each declaration that is left for
                      -- declarations that are still needed
                      let dupsRemove = removeDups wh decls
                      moreDecls <- checkRestDecls decls dupsRemove
                      return (nub (decls++moreDecls))
                        where
                          removeDups [] ys = []
                          removeDups (x:xs) ys
                            | x `elem` ys = removeDups xs ys
                            | otherwise   = x : removeDups xs ys
removeRedunWhere2 wh (exp@(_)) = do
                      (free, dec) <- hsFreeAndDeclaredPNs exp
                      let decls = checkFree2 free wh
                      -- check each declaration that is left for
                      -- declarations that are still needed
                      moreDecls <- checkRestDecls decls wh

                      return (nub (decls++moreDecls))

checkRestDecls [] _ = return []
checkRestDecls wh [] = return []
checkRestDecls ((Dec (HsPatBind loc1 ps (HsBody e) ds)):rest) (x:[])
                      = do
                          (free, dec) <- hsFreeAndDeclaredPNs e
                          let decls = checkFree free [x]
                          return decls

checkRestDecls ((Dec (HsPatBind loc1 ps (HsBody e) ds)):rest) (x:xs)
                      = do
                          (free, dec) <- hsFreeAndDeclaredPNs e
                          let decls = checkFree free (x:xs)
                         -- moreDecls <- checkRestDecls [x] xs
                          moreDecls <- checkRestDecls decls (x:xs)
                          moreDecls' <- checkRestDecls rest (x:xs)
                          return (decls ++ (moreDecls ++ moreDecls'))

checkRestDecls ((Dec (HsFunBind loc1 ms)):rest) (x:xs)
  = do
       res <- checkRestMatches ms
       let newDec = (Dec (HsFunBind loc1 res))
       moreDecls <- checkRestDecls rest (x:xs)
       return (newDec :  moreDecls)
    where
      checkRestMatches [] = return []
      checkRestMatches (m@(HsMatch l i1 ps (HsBody e) ds):ms)
                      = do

                          (free, dec) <- hsFreeAndDeclaredPNs e
                          let decls = checkFree free (x:xs)
                         -- moreDecls <- checkRestDecls [x] xs
                          moreDecls1 <- checkRestMatches ms
                          return moreDecls1


doRemoving1 exp newExp wh (_, _, mod)
 = do
      newMod <- doRemoving exp newExp wh mod
      return newMod


-- Stafunski function to traverse the AST and find the occurance of the exp that we
-- are interested in. When the exp is found, the redundant declarations are calculated
-- and rmDecls in then called.
-- the rusult is then a new expression with the new list of declarations returned by
-- rmDecls.
doRemoving exp newExp wh mod
    =  applyTP (stop_tdTP (failTP `adhocTP` (rmInLet newExp))) mod

           where
             rmInLet (new::HsExpP) (letExp@(Exp (HsParen (Exp (HsCase e2 alts2))))::HsExpP)
                |sameOccurrence letExp exp
                    = do
                         -- error $ show new
                         r <- update letExp (Exp (HsParen new)) letExp
                         return r
                | otherwise = return (Exp (HsParen new))

             rmInLet (new::HsExpP) (letExp@(Exp (HsCase e2 alts2))::HsExpP)
                | rmLocs letExp == rmLocs exp
                    = do
                         -- error $ show new
                         r <- update letExp new letExp
                         return r
                | otherwise = return letExp

             rmInLet (new@(Exp (HsParen e1))::HsExpP) (letExp@(Exp (HsLet ds e))::HsExpP)
               = do
                    res <- rmInLet e1 letExp
                    return res

             rmInLet (new@(Exp (HsLet ds e1))::HsExpP) (letExp@(Exp (HsParen (Exp (HsLet ds2 e2))))::HsExpP)
               | sameOccurrence letExp exp == True
                  = do
                     res <- update letExp (Exp (HsParen new)) letExp
                     return res
               | otherwise = return letExp

             --1. The definition to be removed is a local declaration in a let expression
             rmInLet (new@(Exp (HsLet decs e'))::HsExpP) (letExp@(Exp (HsLet ds e))::HsExpP)
               | sameOccurrence letExp exp == True
                  =do
                      let redunDecs = ds \\ decs
                      ds'<- rmDecls ds redunDecs
                      if ds'==[] then do res <- rmInLet new e
                                         -- r <- update letExp res exp
                                         -- error $ show (tokenise (Pos 0 v1 1) offset False $ printFun)
                                         return res
                                 else do
                                         r <- update letExp (Exp (HsLet ds' e')) letExp
                                         return r
               | otherwise = do
                                    -- error $ show (new, letExp)
                                    return letExp



             rmInLet e1 (Exp (HsLet ds e)::HsExpP)
               | sameOccurrence e1 e == True
                  = do
                      ds' <- rmDecls ds ds
                      if ds' == [] then return e1
                                   else return (Exp (HsLet ds' e))
               | otherwise
                   = return e

             rmInLet (new@(Exp (HsParen (Exp (HsLambda ds1 e1))))::HsExpP) (lamExp@(Exp (HsParen (Exp (HsLambda ds e2))))::HsExpP)
              | sameOccurrence lamExp exp == True
                = do
                     res <- update lamExp new lamExp
                     return res
              | otherwise = return lamExp

             rmInLet (new@(Exp (HsParen e1))::HsExpP) (lamExp@(Exp (HsLambda ds e2))::HsExpP)
               = do
                    res <- rmInLet e1 lamExp
                    return res

             rmInLet (new@(Exp (HsLambda decs e'))::HsExpP) (letExp@(Exp (HsParen (Exp (HsLambda ds e))))::HsExpP)
               | sameOccurrence letExp exp == True
                  =do
                     res <- update letExp (Exp (HsParen new)) letExp
                     return res
               | otherwise = return letExp


             rmInLet (new@(Exp (HsLambda decs e'))::HsExpP) (letExp@(Exp (HsLambda ds e))::HsExpP)
               | sameOccurrence letExp exp == True
                  =do
                     res <- update letExp newExp letExp
                     return res
               | otherwise =  return letExp



      {-       rmInLet (e1@(Exp (HsLambda _ _))::HsExpP) (e2::HsExpP)
                = do res <- update e2 newExp e2
                     return res     -}

             rmInLet e1 e2@(Exp (HsInfixApp e11 o e22)::HsExpP)
                | findEntity e1 e11 = do  -- error $ show (e1, e11)
                                          res <- rmInLet e1 e11
                                          r <- update e2 res e2
                                          return r
                | findEntity e1 e22 = do
                                          res <- rmInLet e1 e22
                                          r <- update e2 res e2
                                          return r

             rmInLet e1 e2@(Exp (HsParen e))
               = do
                    res <- rmInLet e1 e
                    -- r <- update e2 res e2
                    return res

             rmInLet e1 e2
               | sameOccurrence e2 exp == True
                             = do
                                  res <- update e2 e1 e2
                                  return res
               | otherwise   = return e2

             rmDecls wh [] = return wh
             rmDecls wh ((d@(Dec (HsPatBind loc1 pn (HsBody rhs) ds))::HsDeclP):xs)
                  = do
                      let newName = pNTtoPN (patToPNT pn)
                      decls' <- rmDecl newName False wh
                      decls'' <- rmDecls decls' xs
                      return decls''
             rmDecls d _ = return wh


doRemovingWhere exp newExp wh (_,_,mod)
     = (applyTP (stop_tdTP (failTP `adhocTP` (rmInPat exp)
                                   `adhocTP` (rmInMatch exp))) mod)

     {- runStateT (applyTP (stop_tdTP (failTP `adhocTP` (rmInPat exp)
                                              `adhocTP` (rmInMatch exp)
                                              `adhocTP` rmInCase)) mod) ((tokList,unmodified),fileName) -}
          where
             rmInCase (a@(HsAlt s p1 (HsBody e2) ds)::HsAltP)
                | findEntity newExp e2
                   =do
                       -- error $ show e2
                       ds' <- removeRedunWhere ds newExp

                       -- let redunDecs = ds \\ wh
                       -- ds'<- rmDecls ds [] redunDecs
                       -- let ds' = filter (not . (\x -> x `elem` redunDecs)) ds
                       -- error $ show ds'
                       if ds' == [] then fail ""
                                    else do
                                      r <- update a (HsAlt s p1 (HsBody e2) ds') a
                                      -- return (HsAlt s p1 (HsBody e2) ds')
                                      return r
             rmInCase e2 = fail ""
             rmInPat exp (pat@(Dec (HsPatBind loc p (HsBody rhs) ds))::HsDeclP)
                | sameOccurrence exp rhs && ds /= []
                   =do
                       --  error "3"
                       redunDecs2 <- removeRedunWhere ds newExp
                       let redunDecs = ds \\ redunDecs2
                       ds'<- rmDecls ds redunDecs
                       return (Dec (HsPatBind  loc p (HsBody rhs) ds'))
                | sameOccurrence exp rhs && ds == [] && wh /= []
                   = do
                         -- error "2"
                         r <- update pat (Dec (HsPatBind  loc p (HsBody rhs) wh)) pat
                         return r
             rmInPat exp (pat@(Dec (HsPatBind loc p g@(HsGuard es) ds))::HsDeclP)
                | checkES exp es && ds /= []
                   =do
                       --  error "3"
                       redunDecs2 <- removeRedunWhere ds newExp
                       -- circle through all expressions in guards
                       let firstExp = getExp' es
                       redunDecs3 <- removeRedunWhere ds firstExp
                       gatherRedun <- getExp ds (tail es)
                       -- error $ show (redunDecs2, redunDecs3)
                       let redunDecs = nub (((ds \\ redunDecs2) \\ redunDecs3) \\ gatherRedun)
                       ds'<- rmDecls ds redunDecs
                       return (Dec (HsPatBind loc p g ds'))
                | checkES exp es && ds == [] && wh /= []
                   = do
                         -- error "2"
                         r <- update pat (Dec (HsPatBind  loc p g wh)) pat
                         return r
             rmInPat _ e2 = fail ""
             rmInMatch exp  (match@(HsMatch loc1  pnt pats (rhs@(HsBody e)) ds)::HsMatchP)
                | sameOccurrence exp e && wh /= []
                   = do
                        -- ds'' <- addDecl (HsMatch loc1 pnt pats rhs ds) Nothing ((nub (wh++ds)), Nothing) False
                        ds' <- rmDecls ds ds
                        ds'' <- addDecl (HsMatch loc1 pnt pats rhs ds') Nothing (wh, Nothing) False
                        return ds''
                | sameOccurrence exp e && ds /= []
                   =do
                       redunDecs2 <- removeRedunWhere (nub (ds++wh)) newExp
                       let redunDecs = (ds \\ redunDecs2)
                       ds'<- rmDecls ds redunDecs2
                       -- error $ show redunDecs
                       return (HsMatch loc1 pnt pats rhs ds')

                | sameOccurrence exp e && ds == [] && wh /= []
                    = do
                         -- error (show wh)
                         ds' <- addDecl match Nothing (wh, Nothing) False
                         return ds'
             rmInMatch exp  (match@(HsMatch loc1  pnt pats (rhs@(HsGuard es)) ds)::HsMatchP)
              | checkES exp es && ds /= []
                  =do
                       redunDecs2 <- removeRedunWhere (nub (ds++wh)) newExp
                       -- circle through all expressions in guards
                       let firstExp = getExp' es
                       redunDecs3 <- removeRedunWhere ds firstExp
                       gatherRedun <- getExp ds (tail es)
                       -- error $ show (redunDecs2, redunDecs3)
                       let redunDecs = nub (((ds \\ redunDecs2) \\ redunDecs3) \\ gatherRedun)
                       ds'<- rmDecls ds redunDecs
                       -- error $ show redunDecs
                       return (HsMatch loc1 pnt pats rhs ds')

              | checkES exp es && ds == [] && wh /= []
                    = do
                         -- error (show wh)
                         ds' <- addDecl match Nothing (wh, Nothing) False
                         return ds'

             rmInMatch _ e2 = fail ""

             checkES _ [] = False
             checkES exp ((_,_, e):gs)
               | sameOccurrence exp e = True
               | otherwise            = checkES exp gs

             getExp ds [] = return []
             getExp ds ((_,e1,e2):gs)
               = do
                    redunDecs1 <- removeRedunWhere ds e1
                    redunDecs2 <- removeRedunWhere ds e2
                    rest <- getExp ds gs
                    return ((redunDecs1 \\ redunDecs2) \\ rest)

             getExp' [] = defaultExp
             getExp' ((_,e1,_):es) = e1
             --error ((show e1) ++ " " ++ (show e2)  )
             rmDecls wh [] = return wh
             rmDecls wh ((d@(Dec (HsPatBind loc1 pn e ds))::HsDeclP):xs)
                  = do
                      let newName = pNTtoPN (patToPNT pn)
                      decls' <- rmDecl newName False wh
                      decls'' <- rmDecls decls' xs
                      return decls''
             rmDecls wh ((d@(Dec (HsFunBind _ ((HsMatch loc pnt pats e ds):ms)))::HsDeclP):xs)
                  = do
                      let newName = pNTtoPN pnt
                      decls' <- rmDecl newName False wh
                      decls'' <- rmDecls decls' xs
                      return decls''
             rmDecls d _ = return wh

           {-  rmDecls wh d [] = return []
             rmDecls wh d (((Dec (HsPatBind loc1 pn (HsBody rhs) ds))::HsDeclP):xs)
                  = do
                      let newName = pNTtoPN (patToPNT pn)
                      decls' <- rmDecl newName False wh
                      decls'' <- rmDecls wh decls' xs
                      return decls''
             rmDecls _ d _ = return d -}

newMatch loc pnt pats rhs ds = HsMatch loc pnt pats (HsBody rhs) ds
newDecl loc pnt pats rhs ds = Dec (HsFunBind loc [HsMatch loc pnt pats (HsBody rhs) ds] )

checkFree :: [PName] -> [HsDeclP] -> [HsDeclP]
checkFree [] _ = []
checkFree _ [] = []
checkFree (p:ps) list = (checkSin p list) ++ (checkFree ps list)
                                 where
                                   checkSin :: PName -> [HsDeclP] -> [HsDeclP]
                                   checkSin p [] = []
                                   checkSin p (x:xs)
                                      | defines p x = [x]
                                      | otherwise   = checkSin p xs

checkFree2 :: [PName] -> [HsDeclP] -> [HsDeclP]
checkFree2 [] _ = []
checkFree2 _ [] = []
checkFree2 (p:ps) list = (checkSin p list) ++ (checkFree ps list)
                                 where
                                   checkSin :: PName -> [HsDeclP] -> [HsDeclP]
                                   checkSin p [] = []
                                   checkSin p (x:xs)
                                      | defines' p x = x : (checkSin p xs)
                                      | otherwise   = checkSin p xs


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
      inMatch (match@(HsMatch loc1  pnt pats rhs@(HsBody e) ds)::HsMatchP)
        | locToExp beginPos endPos toks rhs /= defaultExp
          = Just ([loc1], pnt, pats, e, ds, (Match match))
      inMatch (match@(HsMatch loc1 pnt pats (rhs@(HsGuard es)) ds)::HsMatchP)
          = checkES es
                where
                   checkES [] = Nothing
                   checkES ((s, e1 , e): es)
                     | locToExp beginPos endPos toks e /= defaultExp
                          = Just ([loc1], pnt, pats, e, ds, (Match match))
                     | otherwise = checkES es
      inMatch x = Nothing

      --The selected sub-expression is in the rhs of a pattern-binding
      inPat (pat@(Dec (HsPatBind loc1 ps (rhs@(HsBody e)) ds))::HsDeclP)
        | locToExp beginPos endPos toks rhs /= defaultExp
          = if isSimplePatBind pat
              then Just ([loc1], patToPNT ps, [], e, ds, (MyPat pat))
              else error "Please select the result of the function!"
      inPat (pat@(Dec (HsPatBind loc1 ps (rhs@(HsGuard es)) ds))::HsDeclP)
        = checkES es
            where
               checkES [] = Nothing
               checkES ((s, e1 , e): es)
                 | locToExp beginPos endPos toks e /= defaultExp
                      = Just ([loc1], patToPNT ps, [], e, ds, (MyPat pat))
                 | otherwise = checkES es
      inPat _ = Nothing



