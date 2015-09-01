

module RefacRmCon(refacRmCon) where

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
import PFE0 (findFile)
import MUtils (( # ))
import RefacLocUtils
-- import System
import System.IO

{- This refactoring removes a user selected constructor from a data type and resolves all pattern matching.

   When a constructor is removed, all equations over that value will be commented out; all references to that value within an expression will be replaced with a call to error.

   Copyright   :  (c) Christopher Brown 2008

   Maintainer  :  cmb21@kent.ac.uk
   Stability   :  provisional
   Portability :  portable

-}

data Decls = PatBind HsDeclP | MatchBind HsMatchP deriving (Read, Show, Eq)

refacRmCon args
 = do let fileName = ghead "filename" args
          --fileName'= moduleName fileName
          --modName  = Module fileName'
          row      = read (args!!1)::Int
          col      = read (args!!2)::Int
      modName <-fileNameToModName fileName
      (inscps, exps, mod, tokList)<-parseSourceFile fileName
      case checkCursor fileName row col mod of
        Left errMsg -> do error errMsg
        Right dat ->
          do
           let pnt = locToPNT fileName (row, col) mod
           if (pnt /= defaultPNT)
            then
             if isDataCon pnt
               then do
                    let (pnts, defDecl) = pntsToBeRemoved pnt mod
                    if isExported (declToPNT defDecl) exps
                      then do
                              clients <- clientModsAndFiles modName
                              info    <- mapM parseSourceFile $ map snd  clients
                              ((_,m), (newToks, newMod))<-applyRefac (doRemoving pnt defDecl modName)
                                                                      (Just (inscps, exps, mod, tokList)) fileName
                              refactoredClients<-mapM (removeInClientMod pnt defDecl modName) $ zip info (map snd clients)
                              writeRefactoredFiles False $ ((fileName,m),(newToks,newMod)):refactoredClients
                              AbstractIO.putStrLn "\nCompleted.\n"
                      else do
                              ((_,m), (newToks, newMod))<-applyRefac (doRemoving pnt defDecl modName)
                                                                     (Just (inscps, exps, mod, tokList)) fileName
                              writeRefactoredFiles False [((fileName,m), (newToks,newMod))]
                              AbstractIO.putStrLn "\nCompleted.\n"
               else error "Please select a constructor!"
             else
              error "\nInvalid cursor position!"

checkCursor :: String -> Int -> Int -> HsModuleP -> Either String HsDeclP
checkCursor fileName row col mod
 = case locToTypeDecl of
     Nothing -> Left ("Invalid cursor position. Please place cursor at the beginning of the constructor name!")
     Just decl@(Dec (HsDataDecl loc c tp xs _)) -> Right decl
   where
    locToTypeDecl = find (definesTypeCon (locToPNT fileName (row, col) mod)) (hsModDecls mod)

    -- definesTypeCon pnt (Dec (HsDataDecl loc c tp xs _))
    --  = isDataCon pnt && (findPNT pnt tp)

    definesTypeCon pnt (Dec (HsDataDecl _ _ _ i _))
      = isDataCon pnt && (findPNT pnt i)
    definesTypeCon pnt _ = False


removeInClientMod pnt defDecl modName ((inscps, exps, mod,ts), fileName)
 = do
       ((_,m), (newToks, newMod))<-applyRefac (doRemoving2 pnt defDecl modName)
                                              (Just (inscps, exps, mod, ts)) fileName
       return ((fileName, m), (newToks, newMod))

doRemoving2 pnt defDecl modName (_, exps, t)
  = do
       mod''  <- removePatEquation pnt defDecl modName exps t
       mod''' <- replaceOrdPats pnt defDecl mod''

       return mod'''


doRemoving pnt defDecl modName (_, exps, t)
  = do mod'   <- removeConstr pnt defDecl t
       mod''  <- removePatEquation pnt defDecl modName exps mod'
       mod''' <- replaceOrdPats pnt defDecl mod''

       return mod'''

createError :: String -> String -> Int -> HsExpP
createError newE typeName line
   = (Exp (HsApp (nameToExp "error") (nameToExp ("\""++newE++" no longer defined for "++typeName++" at line: "++(show line)++"\""))))


pntToLine pnt = let (SrcLoc fileName _ row col) = (useLoc pnt) in row

-- replace normal expression patterns with call to error
replaceOrdPats pnt defDecl t
  = applyTP (stop_tdTP (failTP `adhocTP` rmInExp)) t
      where
        rmInExp e@(Exp (HsId (HsCon x)))
         | defineLoc x == defineLoc pnt
             = do
                  let newE = (render.ppi) e
                  let typeName = declToName defDecl
                  let line = pntToLine pnt
                  update e (Exp (HsParen (createError newE typeName line))) e
        rmInExp e@(Exp (HsInfixApp e1 o@(HsCon x) e2 ))
         | defineLoc x == defineLoc pnt
             = do
                  let newE = (render.ppi) e
                  let typeName = declToName defDecl
                  let line = pntToLine pnt
                  update e (Exp (HsParen (createError newE typeName line))) e
        rmInExp x = mzero

-- comment out all equations referencing removed
-- constructor
removePatEquation pnt defDecl modName exps t
  = applyTP (full_buTP (idTP   `adhocTP` rmInMod
                               `adhocTP` rmInMatch
                               `adhocTP` rmInPat
                               `adhocTP` rmInLet
                               `adhocTP` rmInAlt
                               `adhocTP` rmInLetStmt
                               `adhocTP` rmInMonad
                               )) t
   where
     -- 1. the equation to comment out is on the top level of a definition...
     rmInMod (mod@(HsModule loc name exps imps ds):: HsModuleP)
       | canBeRemoved pnt mod
                  =do
                      let declsToRemove = whatCanBeRemoved pnt mod
                      ds' <- rmDecls declsToRemove ds
                      -- do we need to comment out the type signature
                      -- of any entities?
                      dsCommented <- comTypeSigs ds' (HsModule loc name exps imps ds') ds'
                      -- check for calls to deleted definitions
                      let removedElems = ds \\\ dsCommented
                      dsReplacedCall <- checkCalls removedElems dsCommented
                      -- check that deleted defintion is not exported...
                      return (HsModule loc name exps imps dsReplacedCall)
     rmInMod x = return x

     --2. The definition to be removed is a local declaration in a match
     rmInMatch (match@(HsMatch loc name pats rhs ds)::HsMatchP)
       | canBeRemoved pnt match
                   =do
                       let declsToRemove = whatCanBeRemoved pnt match
                       ds'<-rmDecls declsToRemove ds
                       dsCommented <- comTypeSigs ds' (HsMatch loc name pats rhs ds') ds'
                       let removedElems = ds \\\ dsCommented
                       rhsReplacedCall <- checkCalls removedElems rhs
                       return (HsMatch loc name pats rhsReplacedCall dsCommented)
     rmInMatch x =return x

     --3. The definition to be removed is a local declaration in a pattern binding
     rmInPat (pat@(Dec (HsPatBind loc p rhs ds))::HsDeclP)
       | canBeRemoved pnt pat
                   =do
                       let declsToRemove = whatCanBeRemoved pnt pat
                       ds'<- rmDecls declsToRemove ds
                       dsCommented <- comTypeSigs ds' (Dec (HsPatBind loc p rhs ds')) ds'
                       let removedElems = ds \\\ dsCommented
                       rhsReplacedCall <- checkCalls removedElems rhs
                       return (Dec (HsPatBind  loc p rhsReplacedCall dsCommented))
     rmInPat x =return x

     --4.The definition to be removed is a local declaration in a let expression
     rmInLet (letExp@(Exp (HsLet ds e))::HsExpP)
       | canBeRemoved pnt letExp
                  = do
                       let declsToRemove = whatCanBeRemoved pnt letExp
                       ds'<- rmDecls declsToRemove ds
                       if ds'==[] then return e
                                  else do dsCommented <- comTypeSigs ds' (Exp (HsLet ds' e)) ds'
                                          let removedElems = ds \\\ dsCommented
                                          eReplacedCall <- checkCalls removedElems e
                                          return (Exp (HsLet dsCommented eReplacedCall))
     rmInLet (letExp@(Exp (HsListComp (HsLetStmt ds stmts))))  -- e.g. [0|z=1] => [0]
       | canBeRemoved pnt letExp
                 =do
                     let declsToRemove = whatCanBeRemoved pnt letExp
                     ds'<- rmDecls declsToRemove ds
                     dsCommented <- comTypeSigs ds' (Exp (HsListComp (HsLetStmt ds' stmts))) ds'
                     let removedElems = ds \\\ dsCommented
                     sReplacedCall <- checkCalls removedElems stmts
                     if ds'/=[]
                         then return (Exp (HsListComp (HsLetStmt dsCommented sReplacedCall)))
                         else if isLast stmts
                                then return (Exp (HsList [fromJust (expInLast sReplacedCall)]))
                                else return (Exp (HsListComp sReplacedCall))
     rmInLet x = return x

     --5. The defintion to be removed is a local decl in a case alternative.
     rmInAlt (alt@(HsAlt loc p rhs ds)::HsAltP)
       |canBeRemoved pnt alt
           =do
               let declsToRemove = whatCanBeRemoved pnt alt
               ds'<- rmDecls declsToRemove ds
               dsCommented <- comTypeSigs ds' (HsAlt loc p rhs ds') ds'
               let removedElems = ds \\\ dsCommented
               rhsReplacedCall <- checkCalls removedElems rhs
               return (HsAlt loc p rhsReplacedCall dsCommented)
     rmInAlt x = return x

     --6. The definition to be removed is a local decl in a let statement.
     rmInLetStmt (letStmt@(HsLetStmt ds stmts)::(HsStmt (HsExpP) (HsPatP) [HsDeclP]))
       |canBeRemoved pnt letStmt
          =do
              let declsToRemove = whatCanBeRemoved pnt letStmt
              ds'<- rmDecls declsToRemove ds
              dsCommenting <- comTypeSigs ds' (HsLetStmt ds' stmts) ds'
              let removedElems = ds \\\ dsCommenting
              sReplacedCall <- checkCalls removedElems stmts
              if ds'==[]  then return sReplacedCall
                          else return (HsLetStmt dsCommenting sReplacedCall)
     rmInLetStmt x = return x

     --7. If the definition occurs within a pattern binding in a monadic expression
     -- give an error.
     rmInMonad (letStmt@(HsLetStmt ds stmts)::HsStmtP)
       |canBeRemoved pnt letStmt
          =do
              let declsToRemove = whatCanBeRemoved pnt letStmt
              ds'<- rmDecls declsToRemove ds
              dsCommenting <- comTypeSigs ds' (HsLetStmt ds' stmts) ds'
              let removedElems = ds \\\ dsCommenting
              sReplacedCall <- checkCalls removedElems stmts
              if ds'==[]  then return sReplacedCall
                          else return (HsLetStmt dsCommenting sReplacedCall)

     rmInMonad (mon@(HsGenerator s p e stmts)::HsStmtP)
       | (defineLoc pnt) `elem` flatternPat p
             = error "Refactoring cannot be performed as constructor is used in a pattern binding!"   -- [decl]
     rmInMonad x = return x



     -- list1 minus list2
     (\\\) :: [HsDeclP] -> [HsDeclP] -> [HsDeclP]
     (\\\) list1 list2 = convertMatches list1 \\\\ convertMatches list2


     (\\\\) [] _ = []
     (\\\\) (d@(Dec (HsFunBind loc [HsMatch loc2 name _ _ _])):ls) list2
      | name `elem2` list2 = ls \\\\ list2
      | otherwise      = d : ls \\\\ list2
         where
           elem2 _ [] = False
           elem2 name (d@(Dec (HsFunBind loc [HsMatch loc2 name2 _ _ _])):ds)
             | name == name2 = True
             | otherwise     = name `elem2` ds
           elem2 name (d:ds) = name `elem2` ds
     (\\\\) (d:ds) list2
       | d `elem` list2 = ds \\\\ list2
       | otherwise      = d : ds \\\\ list2


     convertMatches :: [HsDeclP] -> [HsDeclP]
     convertMatches [] = []
     convertMatches ((Dec (HsFunBind loc ms)):ds)
               = let toFunBind m = Dec (HsFunBind loc [m])
                 in (map toFunBind ms) ++ (convertMatches ds)
     convertMatches (d:ds) = d : convertMatches ds


     -- checkCalls searched for all identifiers and checks whether their
     -- defining entity still occurs or not.
     -- if not, the identifier is replaced with a call to error
     -- (passing in its parameters via a show)

     checkCalls decs t
        = applyTP (stop_tdTP (failTP   `adhocTP` rmInExp )) t
            where
              rmInExp e@(Exp (HsId (HsVar x)))
               | definingDecls [pNTtoPN x] decs False True /= []
                    = do
                         let newE = (render.ppi) e
                         let typeName = declToName defDecl
                         let line     = pntToLine pnt
                         update e (createError newE typeName line) e



              rmInExp e@(Exp (HsApp e1 e2))
               | concatMap (definingDecls' decs False True) (map expToPN (flatternApp e)) /= []
                = do
                    let newE = (render.ppi) e
                    let typeName = declToName defDecl
                    let line = pntToLine pnt
                    update e (createError newE typeName line) e


              rmInExp x = mzero

              definingDecls' x y z l = definingDecls [l] x y z

              flatternApp :: HsExpP -> [HsExpP]
              flatternApp (Exp (HsApp e1 e2)) = flatternApp e1 ++ flatternApp e2
              flatternApp (Exp (HsParen e)) = flatternApp e
              flatternApp x = [x]




     -- comTypeSigs :: (MonadState (([PosToken], Bool), t1) m, MonadPlus m) => [HsDeclP] -> [HsDeclP] -> m [HsDeclP]
     comTypeSigs [] _ _ = return []
     comTypeSigs (d@(Dec (HsTypeSig _ _ _ _)):ds) e decs
      | not (any (isTypeSigOf' d) (map declToPNT' (hsDecls e)))
           = do -- we must comment out this type signature
                       rest <- comTypeSigs ds e decs
                       ((toks,_),others)<-get
                       let (startPos,(endPosR, endPosC)) = getStartEndLoc toks d
                           (toks', decls')
                               = ((commentToks (startPos, (endPosR, endPosC)) toks),(rest \\ [d]))
                       put ((toks',modified),others)
                       let res = decls'
                       if isExported (declToPNT d) exps
                        then error ("Removing constructor forces " ++ (declToName d) ++ " in module "
                                  ++ (modNameToStr modName) ++ " to be removed. Please un-export it first.")
                        else return res
     --  | otherwise = rmTypeSig ds environ
     comTypeSigs (d:ds) e decs = do
                               rest <- comTypeSigs ds e decs
                               return (d : rest)

     -- | Return True if the declaration defines the type signature of the specified identifier.
     isTypeSigOf' :: HsDeclP -> PNT-> Bool
     isTypeSigOf' (Dec (HsTypeSig loc is c tp)) pnt = elem (rmLocs pnt) (map rmLocs is)
     isTypeSigOf' _  _ =False


     rmDecls :: (MonadState (([PosToken], Bool), t1) m, MonadPlus m)
                 => [Decls] -> [HsDeclP] -> m [HsDeclP]
     rmDecls [] e   = return e
     rmDecls  ((PatBind decl):ds) decls
       = do rest <- rmDecls ds decls
            ((toks,_),others)<-get
            let (startPos,(endPosR, endPosC)) = getStartEndLoc toks decl
                (toks', decls')
                    = ((commentToks (startPos, (endPosR, endPosC)) toks),(rest \\ [decl]))
            put ((toks',modified),others)
            let res = decls'
            return res

     rmDecls ((MatchBind match):ds) decls
      = do rest <- rmDecls ds decls
           ((toks,_),others)<-get
           let (startPos,(endPosR, endPosC)) = getStartEndLoc toks match
               modDecls = removedMatch match rest -- decls
               (toks', decls')
                    = ((commentToks  (startPos, (endPosR, endPosC)) toks), modDecls)
           put ((toks',modified),others)
           let res = decls'
           return res


     removedMatch match decls =
         concatMap (removeMatch match) decls

     removeMatch match decl@(Dec (HsFunBind loc (m:ms)))
       | removesMatches match (m:ms) == [] = []
       | otherwise  = [ (Dec (HsFunBind loc (removesMatches match (m:ms)))) ]
     removeMatch m d = [d]

     removesMatches match [] = []
     removesMatches match (m:ms)
         | sameOccurrence match m = removesMatches match ms
         | otherwise              = m : removesMatches match ms


     isLast (HsLast e)=True
     isLast _=False

     --returns the expression included in the last statement.
     expInLast::HsStmtP->Maybe HsExpP
     expInLast (HsLast e)=Just e
     expInLast _=Nothing



     canBeRemoved pn t
               =let decls=hsDecls t
                    decl=definingDecls2 pnt decls False
                    -- pnames=concatMap definedPNs decl
                    in (decl/=[] && all (not.flip findPNRHS (replaceDecls t (decls \\ decl))) [pNTtoPN pn])

     whatCanBeRemoved pn t
               =let decls=hsDecls t
                    decl=definingDecls1 pnt decls False
                in decl

removeConstr pnt defDecl t
  = applyTP (once_tdTP (failTP `adhocTP` rmInDat)) t

      where
        --1. The constructor is within a data declaration
        rmInDat (dat@(Dec (HsDataDecl a b t c d))::HsDeclP)
          | sameOccurrence dat defDecl = do
                                            let newConstrs = removeConst c (pNTtoPN pnt)
                                            update dat (Dec (HsDataDecl a b t newConstrs d)) dat
        rmInDat _ = mzero


        removeConst [] _ = []
        removeConst (m@(HsConDecl _ _ _ (PNT pname _ _) _):ms) pn
           | pname == pn = (removeConst ms pn)
           | otherwise   = m : (removeConst ms pn)
        removeConst (m@(HsRecDecl _ _ _ (PNT pname _ _) _):ms) pn
           | pname == pn = (removeConst ms pn)
           | otherwise   = m : (removeConst ms pn)

pntsToBeRemoved pnt t
 = let decls=hsDecls t
       decl=definingDecls [pNTtoPN pnt] decls False False
   in (concatMap definedPNsForConstr decl, ghead "pntsToBeRemoved" decl)

--Find those declarations(function/pattern binding and type signature) which reference
-- the constructor on the LHS of the equation

-- if we are removing the last equation then we must also remove the type signature...
definingDecls1::PNT->[HsDeclP]->Bool->[Decls]
definingDecls1 pnt ds incTypeSig=concatMap (defines pnt) ds
      where
       defines pnt decl@(Dec (HsFunBind loc (m:ms)))
         = nub (definesMatches (m:ms))
            where
              definesMatches [] = []
              definesMatches (decl@(HsMatch loc1 (PNT pname ty loc2) pats rhs ds'):ms)
                 | (defineLoc pnt) `elem` (concatMap flatternPat pats)
                                                 = (MatchBind decl) : definesMatches ms
                 | otherwise = definesMatches ms
       defines pnt decl@(Dec (HsPatBind loc p rhs ds))
         | (defineLoc pnt) `elem` flatternPat p = [PatBind decl]


       defines pn decl= []

--Find those declarations(function/pattern binding and type signature) which reference
-- the constructor on the LHS of the equation
definingDecls2::PNT->[HsDeclP]->Bool->[HsDeclP]
definingDecls2 pnt ds incTypeSig=concatMap (defines pnt) ds
      where
       defines pnt decl@(Dec (HsFunBind loc (m:ms)))
         | or (definesMatches (m:ms)) = [decl]
            where
              definesMatches [] = [False]
              definesMatches (decl@(HsMatch loc1 (PNT pname ty loc2) pats rhs ds'):ms)
                 | (defineLoc pnt) `elem` (concatMap flatternPat pats)
                                                        = True : definesMatches ms
                 | otherwise = definesMatches ms
       defines pnt decl@(Dec (HsPatBind loc p rhs ds))
         | (defineLoc pnt) `elem` flatternPat p = error "Refactoring cannot be performed as constructor is used in a pattern binding!"   -- [decl]


       defines pn decl= []

flatternPat :: HsPatP -> [SrcLoc]
flatternPat t
  = inPat t
    where
      inPat (Pat (HsPId (HsVar pnt@(PNT _ _ _)))) = [defineLoc pnt]
      inPat (Pat (HsPInfixApp p1 pnt@(PNT _ _ _) p2))
          = addPat (defineLoc pnt) (concatMap flatternPat [p1,p2])
      inPat (Pat (HsPApp pnt@(PNT _ _ _) pats))=addPat (defineLoc pnt) (concatMap flatternPat pats)
      inPat (Pat (HsPRec pnt@(PNT _ _ _) fields))=[defineLoc pnt]
      inPat (Pat (HsPTuple _ pats)) = concatMap flatternPat pats
      inPat (Pat (HsPList _ pats)) = concatMap flatternPat pats
      inPat (Pat (HsPParen pats) )  = flatternPat pats
      inPat (Pat (HsPAsPat _ pats)) = flatternPat pats
      inPat (Pat (HsPIrrPat pats))  = flatternPat pats
      inPat _ = []

      addPat pat mfd= ([pat] `union` mfd)


