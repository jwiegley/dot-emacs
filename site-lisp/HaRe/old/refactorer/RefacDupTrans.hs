module RefacDupTrans where
import System.IO.Unsafe
import PosSyntax hiding (ModuleName, HsName, SN)
import SourceNames
import ScopeModule
import UniqueNames hiding (srcLoc)
import HsName
import HsLexerPass1
import PNT
import TiPNT
import SimpleGraphs(reverseGraph,reachable)
import HsTokens
import PrettyPrint
import RefacTypeSyn
import RefacLocUtils
import Data.Char
import GHC.Unicode
import AbstractIO
import Data.Maybe
import Data.List
import Data.Function
import RefacUtils
import LocalSettings (classTransformPath,answerFilePath)
import DuplicateCode (foldDo)

type NameToCall    = String
type NameToReplace = String
type Module        = String
type FileName      = String

refacDupTrans args
  = do
       AbstractIO.putStrLn "refacDupTrans"
       {- let fileName = ghead "fileName'" args
           beginRow         = read (args!!1)::Int
           beginCol         = read (args!!2)::Int
           endRow           = read (args!!3)::Int
           endCol           = read (args!!4)::Int
       -- collect the answers...
       (inscps, exps, mod, tokList)<-parseSourceFileOld fileName
       let subExp = locToExp (beginRow, beginCol) (endRow, endCol) tokList mod
       expression <- AbstractIO.readFile transFilePath
       let expressions = (read expression)::([ [(HsExpP, String)] ])

       let clonedExps = concat (filter (subExp `myElem`) expressions)
           groupedClones = groupClones clonedExps  -}

       cloneCall <- AbstractIO.readFile classTransformPath
       answers   <- AbstractIO.readFile answerFilePath

       let clonedExps = pruneCloneClass (read cloneCall::[(HsExpP, String, String)]) (filter (isAlpha) answers)
           groupedClones = groupClones clonedExps

       if clonedExps == []
         then error "Please use introduce a new definition instead; selected expression is not a member of a clone class!"
         else do
            -- make sure all the files we need to modify
            -- are added to the project. Otherwise we run into "module not found"
            -- issues...
            let names = nub $ concatMap (map snd) groupedClones
            mods <- (mapM parseSourceFile names)
            destMods <- mapM fileNameToModName names
            -- addFile names
            res <- createParameters (makeFullASTList mods) 1 (createAbs (map fst clonedExps))
            let pns  = nub $ concatMap definedPNs [(fromJust res)]
            results <- callFindSafeModules destMods (myZip mods names groupedClones) pns res
            writeRefactoredFiles False results
            AbstractIO.putStrLn "Clone Transformation Completed.\n"
makeFullASTList gf= [mod | (inscps, exps, mod, tokList) <- gf]


pruneCloneClass :: [ (HsExpP, String, String) ] -> String -> [ (HsExpP, String) ]
pruneCloneClass ((x,y,z):xs) ('y':ys) = (x,y) : pruneCloneClass xs ys
pruneCloneClass (x:xs) ('n':ys) = pruneCloneClass xs ys
pruneCloneClass _ _ = []


retainLocs [] _ = []
retainLocs _ [] = []
retainLocs ((i,e,_,_):ms) (((_,_),(t,m)):ts)
 = (i,e,m,t) : retainLocs ms ts

myZip :: [(a,b,c,d)] -> [e] -> [f] -> [(a,b,c,d,e,f)]
myZip ((a,b,c,d):as) (e:bs) (f:fs) = (a,b,c,d,e,f) : myZip as bs fs
myZip _      _   _    = []


-- find safe Module
-- this function checks to see where there is a safe place
-- to put the abstraction.
--
-- given the list of the files that we are transforming,
-- we introduce a cyclic inclusion if the module
-- we want to introduce the abstraction already imports
-- another module.... Therefore the module cannot import
-- any of the modules from our transformation set.
-- findSafeModule :: Term t => [ ModuleName ] -> t -> [Bool]
findSafeModule destMods mod
  = not $ or $ map (flip elem mod) (map fst destMods)


findSafeModules destmods [] _ = -- basically we can't do imports, everywhere needs to define abstraction!
                                  return Nothing
findSafeModules destmods ((inscps, exps, mod, tokList, fileName, clonedExps@(c:cs)):mods) res
  = do
          modName <- fileNameToModName fileName
          modules <- serverModsAndFiles modName
          if findSafeModule modules destmods
           then
            do AbstractIO.putStrLn $ show fileName
               -- add the abstraction in this module...
               -- we also need to make sure all other modules import this module...
               ((f,m), (newToks, newMod)) <- applyRefac (addAbstraction res (map fst clonedExps))
                                                        (Just (inscps, exps, mod, tokList)) fileName


               return (Just (((f,m), (newToks, newMod)), mod, fileName))
           else do rest <- findSafeModules destmods mods res
                   return rest


callFindSafeModules destMods mods pns res
 = do
       -- mod is the module that everything has to import...
       result <- findSafeModules destMods mods res
       if result == Nothing
            then error "All will introduce cyclic inclusion!"
            else do let (transformation, m, fName) = fromJust result
                    fFile <- fileNameToModName fName
                    transformation' <- addImports mods res m pns fName fFile
                    -- we also need to transform the module we are left with
                    -- i.e. the module where we have added the abstraction...
                    return (transformation:transformation')

addImports [] _ _ _ _ _ = return []
addImports (t@(inscps, exps, mod, tokList, fileName, clonedExps@(c:cs)):ms) res m pns fFile f
 | mod == m  = do
                  rest <- addImports ms res m pns fFile f
                  return rest
 | otherwise = do modified <- addImports' t res pns fFile f
                  rest <- addImports ms res m pns fFile f
                  return (modified: rest)

addImports' (inscps, exps2, mod, tokList, fileName, clonedExps@(c:cs)) res pns fFile f
 = do
      ((f,m), (newToks, newMod)) <- applyRefac (addImport'' res pns fFile f (map fst clonedExps)) (Just (inscps, exps2, mod, tokList)) fileName
      return ((f,m), (newToks, newMod))


addImport'' res pns fFile f exps (_,_,t)
 = do
      replacedT <- replaceOccurrences t res exps
      t' <- addImport fFile f pns replacedT
      return t'


-- transformClones takes a list of [(HsExpP, String)]
-- parses the module of String, and performs a
-- "addAbstraction" over that module and writes the
-- refactoredFiles.
--
-- transformClones should be called from a mapM_ to allow
-- the monadic effect to be preserved.
transformClones destMods res f clonedExps@(c:cs)
 = do
     let fileName = snd c

     currentMod <- fileNameToModName fileName
     origFile <- fileNameToModName f

     let pns  = nub $ concatMap definedPNs [(fromJust res)]

     (inscps, exps, mod, tokList)<-parseSourceFileOld fileName
     ((f2,m), (newToks, newMod)) <- applyRefac (extractExpression res pns fileName origFile currentMod (map fst clonedExps))
                                               (Just (inscps, exps, mod, tokList)) fileName
     return ((f2,m), (newToks, newMod))


-- group the expressions by their defining module.
-- groupBy :: (a -> a -> Bool) -> [a] -> [[a]]
groupClones :: [ (HsExpP, String) ] -> [ [(HsExpP, String)] ]

groupClones clones
  = groupBy checkFile clones
     where
      checkFile :: Eq b => (a,b) -> (a,b) -> Bool
      checkFile (a,b) (c,d) = b == d


myElem :: HsExpP -> [(HsExpP, String)] -> Bool
myElem _ [] = False
myElem e ((x,y):xs)
 | toRelativeLocs e == toRelativeLocs x    = True
 | otherwise = myElem e xs

extractExpression decs pns fFile f fileName exps (_,_,t)
 | f /= fileName
     = do
      -- find the expressions in t that are associated
      -- with exps. Replace these expressions with a call
      -- to the abstactions.
      replacedT <- replaceOccurrences t decs exps
      return replacedT
 | otherwise = do replacedT <- replaceOccurrences t decs exps
                  return replacedT


--add a definition name to the import. If the module is not imported yet, then create a new import decl.
-- addImport::String->HsName.ModuleName->[PName]->HsModuleP->HsModuleP
addImport destFileName destModName pns mod@(HsModule _ _  _ imp _)
  =if itemIsImportedByDefault destModName mod     -- Is the definition name explicitly imported?
    then return mod                               -- Yes. Do nothing.
    else if itemsAreExplicitlyImported destModName mod  --Is the module imported and some of its items are explicitly imported?
          then addVarItemInImport1 destModName pns mod -- Yes. Then add the definition name to the list.
          else addImportDecl mod (modNameToStr destModName) False  Nothing False (map pNtoName pns)
               --addImportDecl mod (mkImportDecl destFileName destModName  False (map pNtoName pns)) --Create a new import decl.

  where
   {- Compose a import declaration which imports the module specified by 'modName',
      and only imports the definition spcified by 'e'.
    -}

   itemsAreExplicitlyImported serverModName (HsModule _ _ _ imps _)
     = any (isExplicitlyImported serverModName) imps
    where
       isExplicitlyImported serverModName ((HsImportDecl _ (SN modName _) _ _ h)::HsImportDeclP)
         = serverModName == modName && isJust h && not (fst (fromJust h))



-- are items defined in the serverModName imported by the current module by default?
itemIsImportedByDefault serverModName (HsModule _ _ _ imps _)
  = any (isImportedByDefault'  serverModName) imps
  where
    isImportedByDefault' serverModName ((HsImportDecl _ (SN modName _) _ _ h)::HsImportDeclP)
       = serverModName == modName && ( isNothing h  || (isJust h && fst(fromJust h)))


addVarItemInImport1 serverModName pns mod
   = applyTP ((once_tdTP (failTP `adhocTP` inImport))  `choiceTP` idTP) mod
  where
    inImport (imp@(HsImportDecl loc@(SrcLoc fileName _ row col) (SN modName l) qual as (Just (b,ents))):: HsImportDeclP)
      | serverModName == modName && not b
     =
          addItemsToImport serverModName  Nothing (Left (map pNtoName pns)) imp
    inImport x = mzero

addAbstraction decs exps (_,_,t)
  = do

       replacedT <- replaceOccurrences t decs exps
       t' <- addDecl replacedT Nothing (maybeToList decs, Nothing) True
       t'' <- addItemsToExport t' Nothing False (Left (map declToName (maybeToList decs)))
       return t''


-- replaceOccurrences :: (Term t, MonadPlus m, Monad m) => t -> [ HsDeclP ] -> [ [HsExpP] ] -> m t
-- replaceOccurrences t [] _ = return t
replaceOccurrences t _ [] = return t
replaceOccurrences t dec exps
  = do
       res <- repOcc dec exps t
       -- rest <- replaceOccurrences res dec expss
       return res

repOcc Nothing _ t = return t
repOcc (Just dec) es t
  = do
      -- get the expression on the RHS of Abstraction,
      -- and abstraction name for the call.
      let (name, rhs) = getNameAndRHS dec
      newT <- repOcc' name rhs es t
      return newT
       where
         getNameAndRHS (Dec (HsFunBind _ [HsMatch _ name _ (HsBody e) _]))
           = (name, e)

repOcc' _ _ [] t = return t
repOcc' name rhs (x:xs) t
  = do
      res <- applyTP (once_tdTP (failTP `adhocTP` inExp)) t
      -- error $ show x
      rest <- repOcc' name rhs xs res
      return rest
    where
      inExp e@(Exp (HsDo e1))
       = do
             let new = foldAgainstAbs [] x rhs
             -- we need to actually find the bit to update...
             las <- (getStmtList2 rhs)
             -- error $ show las
             if las == []
               then mzero
               else do
                      let (p, newStmts) = foldStmt' (head las) [] (createFunc name (rmAllLocs new)) e1 x
                      if p
                       then
                        do
                           -- error $ show (e1, rhs)
                           --    new' = (render.ppi) new
                           -- n' <- update e (Exp (HsDo (HsLast (createFunc name new)))) e
                           -- n' <- RefacUtils.delete e e
                           lift $ AbstractIO.putStrLn $ show new
                           n'' <- update e (Exp (HsDo newStmts))  e
                           return n''
                       else mzero

      inExp e@(Exp (HsParen e1))
        | sameOccurrence e x
            = do
                 let new = foldAgainstAbs [] e rhs
                     new' = (render.ppi) new

                 e' <- update e (Exp (HsParen (createFunc name new))) e
                 return e'

       -- | otherwise = mzero
      inExp (e::HsExpP)
        | sameOccurrence e x
            = do
                 let new = foldAgainstAbs [] e rhs
                     new' = (render.ppi) new
                 e' <- update e (createFunc name new) e
                 return e'
      inExp e =
                   mzero

getStmtList2 (Exp (HsDo s))
  = return [last $ getStmtList s]
getStmtList2 _ = return []


foldStmt' :: HsStmtAtomP -> [HsPatP] -> HsExpP -> HsStmtP -> HsExpP -> (Bool, HsStmtP)
foldStmt' ss p e s (Exp (HsDo s1)) = foldStmt ss p e  s s1
foldStmt' ss p e s1 _ = (False, s1)

foldStmt :: HsStmtAtomP -> [HsPatP] -> HsExpP -> HsStmtP -> HsStmtP -> (Bool, HsStmtP)
foldStmt ss p e s1@(HsGenerator _ p1 e1 s0) s2@(HsGenerator _ p2 e2 s3)
 | p1 == p2 && sameOccurrence e1 e2 = foldStmt ss (p++[p1]) e s0 s3
 | otherwise = (False, s1)
foldStmt (HsLastAtom ee) p e s1@(HsQualifier e1 s3) (HsLast e2)
 | isReturn ee && e2 == defaultExp = (True, newStmt)
 | sameOccurrence e1 e2 = (True, s1)
      where
          newStmt = (HsGenerator loc0 (Pat (HsPTuple loc0 p)) e s3)
foldStmt ee p e s1@(HsQualifier e1 s0) s2@(HsQualifier e2 s3)
 | sameOccurrence e1 e2 = foldStmt ee p e s0 s3
 | otherwise = (False, s1)
foldStmt (HsLastAtom ee) p e s1@(HsLast e1) s2@(HsLast e2)
 | isReturn ee && e2 == defaultExp = (True, newStmt)
 | e2 == defaultExp = (True, s1)
 | sameOccurrence e1 e2 && isReturn ee = (True, newStmt)
 | sameOccurrence e1 e2 = (True, s1)
         where
            newStmt = (HsGenerator loc0 (Pat (HsPTuple loc0 p)) e s1)
foldStmt ee p e s1 s2 = (False, s1)

isReturn e = (render.ppi) (head (flatternApp e)) == "return"
flatternApp :: HsExpP -> [HsExpP]
flatternApp (Exp (HsApp e1 e2)) = flatternApp e1 ++ flatternApp e2
flatternApp (Exp (HsParen e)) = flatternApp e
flatternApp x = [x]

grabPNT :: PNT -> [PNT] -> PNT
grabPNT x [] = x
grabPNT x (y:ys)
  | defineLoc x == defineLoc y = y
  | otherwise = grabPNT x ys

checkPNTInPat :: [HsPatP] -> PNT -> Bool
checkPNTInPat [] _ = False
checkPNTInPat (p:ps) i
        | defineLoc i == (SrcLoc "__unknown__" 0 0 0) = False
        | defineLoc i == defineLoc (patToPNT p) = True
        | otherwise = checkPNTInPat ps i

foldAgainstAbs :: [HsPatP] -> HsExpP -> HsExpP -> [ HsExpP ]
foldAgainstAbs _ e1 e2
 | e1 == defaultExp || e2 == defaultExp = []
foldAgainstAbs pats e@(Exp (HsId (HsVar x))) (Exp (HsId (HsVar y)))
 | x == y && isTopLevelPNT x = []
 | x == y && isTopLevelPNT x = []
 | checkPNTInPat pats x  = []
 | otherwise = [e]
foldAgainstAbs pats e@(Exp (HsId (HsCon x))) (Exp (HsId (HsCon y)))
  | x == y    = []
  | otherwise = [e]
foldAgainstAbs pats e@(Exp (HsLit s l1)) (Exp (HsLit s2 l2))
  | l1 == l2  = []
  | otherwise = [(Exp (HsLit loc0 l1))]
foldAgainstAbs pats e@(Exp (HsInfixApp e1 o1 e2)) (Exp (HsInfixApp e3 o2 e4))
  = (e1' ++ o1' ++ e2')
     where
       e1' = foldAgainstAbs pats e1 e3
       o1'
        | o1 == o2  = []
        | otherwise = [Exp (HsId o1)]
       e2' = foldAgainstAbs pats e2 e4
foldAgainstAbs pats e@(Exp (HsApp e1 e2)) (Exp (HsApp e3 e4))
 = (foldAgainstAbs pats e1 e3) ++ (foldAgainstAbs pats e2 e4)
foldAgainstAbs pats e@(Exp (HsNegApp s1 e1)) (Exp (HsNegApp s2 e2))
 = (foldAgainstAbs pats e1 e2)
foldAgainstAbs pats1 e@(Exp (HsLambda pats e1)) (Exp (HsLambda pats2 e2))
 = []
foldAgainstAbs pats e@(Exp (HsLet decs e1)) (Exp (HsLet decs2 e2))
 = (foldAgainstAbs pats e1 e2)
foldAgainstAbs pats e@(Exp (HsIf e1 e2 e3)) (Exp (HsIf e4 e5 e6))
 = (e1' ++ e2' ++ e3')
    where
     e1' = foldAgainstAbs pats e1 e4
     e2' = foldAgainstAbs pats e2 e5
     e3' = foldAgainstAbs pats e3 e6
foldAgainstAbs pats e@(Exp (HsCase e1 alts1)) (Exp (HsCase e2 alts2))
  = []
foldAgainstAbs pats e@(Exp (HsParen e1)) (Exp (HsParen e2))
 = (foldAgainstAbs pats e1 e2)
foldAgainstAbs pats (Exp (HsParen e1)) e2
 = foldAgainstAbs pats e1 e2
foldAgainstAbs pats e1 (Exp (HsParen e2))
 = foldAgainstAbs pats e1 e2
foldAgainstAbs pats (Exp (HsTuple es1)) (Exp (HsTuple es2))
 = concat (foldAgainstAbs' pats es1 es2)
foldAgainstAbs pats (Exp (HsList es1)) (Exp (HsList es2))
 = concat (foldAgainstAbs' pats es1 es2)
foldAgainstAbs pats (Exp (HsLeftSection e1 o1)) (Exp (HsLeftSection e2 o2))
 = e1' ++ o1'
   where
      e1' = foldAgainstAbs pats e1 e2
      o1'
       | o1 == o2 = []
       | otherwise = [Exp (HsId o1)]
foldAgainstAbs pats (Exp (HsRightSection o1 e1)) (Exp (HsRightSection o2 e2))
 = o1' ++ e1'
  where
    e1' = foldAgainstAbs pats e1 e2
    o1'
     | o1 == o2 = []
     | otherwise = [Exp (HsId o1)]
foldAgainstAbs pats (Exp (HsEnumFrom e1)) (Exp (HsEnumFrom e2))
 = foldAgainstAbs pats e1 e2
foldAgainstAbs pats (Exp (HsEnumFromTo e1 e2)) (Exp (HsEnumFromTo e3 e4))
 = foldAgainstAbs pats e1 e2 ++ foldAgainstAbs pats e3 e4
foldAgainstAbs pats (Exp (HsEnumFromThen e1 e2)) (Exp (HsEnumFromThen e3 e4))
 = foldAgainstAbs pats e1 e2 ++ foldAgainstAbs pats e3 e4
foldAgainstAbs pats (Exp (HsEnumFromThenTo e1 e2 e3)) (Exp (HsEnumFromThenTo e4 e5 e6))
 = foldAgainstAbs pats e1 e4 ++ foldAgainstAbs pats e2 e5 ++ foldAgainstAbs pats e3 e6
foldAgainstAbs pats (Exp (HsAsPat i1 e1)) (Exp (HsAsPat i2 e2))
 = i1' ++ e1'
   where
     e1' = foldAgainstAbs pats e1 e2
     i1'
      | i1 == i2 = []
      | otherwise = [Exp (HsId (HsVar i1))]
foldAgainstAbs pats (Exp (HsIrrPat e1)) (Exp (HsIrrPat e2))
 = foldAgainstAbs pats e1 e2
foldAgainstAbs pats (Exp (HsDo e1)) (Exp (HsDo e2))
 = foldAgainstAbsStmts pats e1 e2
foldAgainstAbs pats e1 e2 = [e1]
foldAgainstAbsAlt pats as _ = as

foldAgainstAbs' pats [] [] = []
foldAgainstAbs' p x  [] = []
foldAgainstAbs' p [] x  = []
foldAgainstAbs' p (e:es) (x:xs) = foldAgainstAbs p e x : foldAgainstAbs' p es xs

foldAgainstAbsStmts pats a@(HsGenerator _ p1 e1 s1) b@(HsGenerator _ p2 e2 s2)
 = foldAgainstAbs (pats++[p1]++[p2]) e1 e2 ++ foldAgainstAbsStmts (pats++[p1]++[p2]) s1 s2
foldAgainstAbsStmts pats (HsQualifier e1 s1) (HsQualifier e2 s2)
 = foldAgainstAbs pats e1 e2 ++ foldAgainstAbsStmts pats s1 s2
foldAgainstAbsStmts pats (HsLast e1) (HsLast e2)
 = foldAgainstAbs pats e1 e2
foldAgainstAbsStmts pats (HsLast e1) (HsQualifier e2 s1)
 = foldAgainstAbs pats e1 e2

-- createParameters :: HsExpP -> HsDeclP
-- createParameters mod n [] = return []
createParameters mods n Nothing = return Nothing
createParameters mods n (Just e)
   = do
        numParams <- countParams e
        let nameParams = mkNewNames (length numParams) e []

        e' <- renameNormals e nameParams
        let newDec = createDec (transformBindings e') nameParams
        return (Just newDec)
        where
          transformBindings (Exp (HsDo stmts))
           = (Exp (HsDo (transformBind [] stmts)))
          transformBindings e = e

          transformBind pats (HsGenerator s p1 e1 stmts)
            = (HsGenerator s p1 e1 (transformBind (pats++[p1]) stmts))
          transformBind pats (HsQualifier e stmts)
            = (HsQualifier e (transformBind pats stmts))
          transformBind pats (HsLast e)
           | e == defaultExp
              = (HsLast (Exp (HsApp (nameToExp "return") (Exp (HsTuple (getPats pats))))))
           | pats /= [] = (HsQualifier e (HsLast (Exp (HsApp (nameToExp "return") (Exp (HsTuple (getPats pats)))))))
           | otherwise = (HsLast e)


          getPats [] = []
          getPats (p:ps) = nameToExp (pNTtoName (patToPNT p)) : getPats ps

          createDec e' nameParams
            = Dec (HsFunBind loc0 [HsMatch loc0 (nameToPNT newName)
                                                (map nameToPat nameParams)
                                                (HsBody e')
                                                [] ])


          newName = mkNewName "abs" (map pNTtoName (hsPNTs mods)) n

          renameNormals e [] = return e
          renameNormals e (x:xs)
             = do
                  e' <- renameANorm e x
                  res <- renameNormals e' xs
                  return res
           where
             renameANorm e x
               = applyTP (once_tdTP (failTP `adhocTP` (inPNT x))) e
             inPNT x (p::PNT)
              | pNTtoName p == "$I" = return (nameToPNT x)
             inPNT _ _ = mzero

          countParams t
            = applyTU (full_tdTU (constTU [] `adhocTU` inPNT)) t
          inPNT (p::PNT)
            | pNTtoName p == "$I" = return [p]
          inPNT x = return []

          mkNewNames :: Int -> HsExpP -> [String] -> [String]
          mkNewNames 0 e names = names
          mkNewNames n e names
            = mkNewNames (n-1) e (result : names)
              where
                result = mkNewName "p" (oldNames ++ names) n
                oldNames = map pNTtoName (hsPNTs e)

posToExp :: (Term t) => [PosToken] -> t -> [(SimpPos, SimpPos)] -> [HsExpP]
posToExp _ _ [] = []
posToExp toks mod ((x,y):xs)
  = locToExp x y toks mod    : posToExp toks mod xs

-- compareExp takes a clone class and tries to
-- figure out which parts can be extracted away or not.

-- we take all the variables out of each expression and compare them
-- the ones that match stay in the abstraction,
createAbs' :: [ HsExpP ] -> [ HsExpP ]
createAbs' [] = []
createAbs' [x] = [compareExp [] x x]
createAbs' (x:y:es)
 = int : createAbs' (y:es)
  where
    int = compareExp [] x y

createAbs'' :: [ HsExpP ] -> Maybe HsExpP
createAbs'' [] = Nothing
createAbs'' [x] = Just x
createAbs'' (x:y:xs)
 = createAbs'' ((compareExp [] x y):xs)

createAbs :: [ HsExpP ] -> Maybe HsExpP
createAbs list
  = let f = createAbs' list in (createAbs'' f)


compareExp :: [HsPatP] -> HsExpP -> HsExpP -> HsExpP
compareExp pats e@(Exp (HsId (HsVar x))) (Exp (HsId (HsVar y)))
  | x == y && isTopLevelPNT x = e
  | checkPNTInPat pats x = e
  | otherwise = (Exp (HsId (HsVar (nameToPNT "$I"))))
compareExp pats e@(Exp (HsId (HsCon x))) (Exp (HsId (HsCon y)))
  | x == y    = e
  | otherwise = (Exp (HsId (HsVar (nameToPNT "$I"))))
compareExp pats e@(Exp (HsLit s l1)) (Exp (HsLit s2 l2))
  | l1 == l2  = e
  | otherwise = (Exp (HsId (HsVar (nameToPNT "$I"))))
compareExp pats e@(Exp (HsInfixApp e1 o1 e2)) (Exp (HsInfixApp e3 o2 e4))
  = Exp (HsInfixApp e1' o1' e2')
     where
       e1' = compareExp pats e1 e3
       o1'
        | o1 == o2  = o1
        | otherwise = HsVar (nameToPNT "$I")
       e2' = compareExp pats e2 e4
compareExp pats e@(Exp (HsApp e1 e2)) (Exp (HsApp e3 e4))
 = Exp (HsApp (compareExp pats e1 e3) (compareExp pats e2 e4))
compareExp pats e@(Exp (HsNegApp s1 e1)) (Exp (HsNegApp s2 e2))
 = Exp (HsNegApp s1 (compareExp pats e1 e2))
compareExp pats1 e@(Exp (HsLambda pats e1)) (Exp (HsLambda pats2 e2))
 = Exp (HsLambda pats (compareExp pats1 e1 e2))
compareExp pats e@(Exp (HsLet decs e1)) (Exp (HsLet decs2 e2))
 = Exp (HsLet decs (compareExp pats e1 e2))
compareExp pats e@(Exp (HsIf e1 e2 e3)) (Exp (HsIf e4 e5 e6))
 = Exp (HsIf e1' e2' e3')
    where
     e1' = compareExp pats e1 e4
     e2' = compareExp pats e2 e5
     e3' = compareExp pats e3 e6
compareExp pats e@(Exp (HsCase e1 alts1)) (Exp (HsCase e2 alts2))
 = Exp (HsCase (compareExp pats e1 e2) (compareAlt pats alts1 alts2))
compareExp pats e@(Exp (HsParen e1)) (Exp (HsParen e2))
 = Exp (HsParen (compareExp pats e1 e2))
compareExp pats (Exp (HsParen e1)) e2
 = compareExp pats e1 e2
compareExp pats e1 (Exp (HsParen e2))
 = compareExp pats e1 e2
compareExp pats (Exp (HsList es1)) (Exp (HsList es2))
 = Exp (HsList (compareExp' pats es1 es2))
compareExp pats (Exp (HsTuple es1)) (Exp (HsTuple es2))
 = Exp (HsTuple (compareExp' pats es1 es2))
compareExp pats (Exp (HsLeftSection e1 i1)) (Exp (HsLeftSection e2 i2))
 = Exp (HsLeftSection (compareExp pats e1 e2) i2')
   where
     i2'
       | i1 == i2 = i1
       | otherwise = HsVar (nameToPNT "$I")
compareExp pats (Exp (HsRightSection i1 e1)) (Exp (HsRightSection i2 e2))
 = Exp (HsRightSection i1' (compareExp pats e1 e2))
   where
     i1'
      | i1 == i2 = i1
      | otherwise = HsVar (nameToPNT "$I" )
compareExp pats (Exp (HsEnumFrom e1)) (Exp (HsEnumFrom e2))
 = Exp (HsEnumFrom (compareExp pats e1 e2))
compareExp pats (Exp (HsEnumFromTo e1 e2)) (Exp (HsEnumFromTo e3 e4))
 = Exp (HsEnumFromTo (compareExp pats e1 e3) (compareExp pats e2 e4))
compareExp pats (Exp (HsEnumFromThen e1 e2)) (Exp (HsEnumFromThen e3 e4))
 = Exp (HsEnumFromThen (compareExp pats e1 e3) (compareExp pats e2 e4))
compareExp pats (Exp (HsEnumFromThenTo e1 e2 e3)) (Exp (HsEnumFromThenTo e4 e5 e6))
 = Exp (HsEnumFromThenTo (compareExp pats e1 e4) (compareExp pats e2 e5) (compareExp pats e3 e6))
compareExp pats (Exp (HsAsPat i1 e1)) (Exp (HsAsPat i2 e2))
 = Exp (HsAsPat i1' (compareExp pats e1 e2))
   where
    i1'
     | i1 == i2 = i1
     | otherwise = (nameToPNT "$I")
compareExp pats (Exp (HsIrrPat e1)) (Exp (HsIrrPat e2))
 = Exp (HsIrrPat (compareExp pats e1 e2))
compareExp pats e1@(Exp (HsDo stmts1)) e2@(Exp (HsDo stmts2))
 = Exp (HsDo (compareStmts pats stmts1 stmts2))
compareExp pats e1 e2 = (Exp (HsId (HsVar (nameToPNT "$I"))))
compareAlt pats as _ = as

compareStmts pats (HsGenerator s p1 e1 s1) (HsGenerator _ p2 e2 s2)
 = HsGenerator s p1 (compareExp (pats++[p1]++[p2]) e1 e2) (compareStmts (pats++[p1]++[p2]) s1 s2)
compareStmts pats (HsQualifier e1 stmts1) (HsQualifier e2 stmts2)
 = HsQualifier (compareExp pats e1 e2) (compareStmts pats stmts1 stmts2)
compareStmts pats (HsLast e1) (HsLast e2)
 = HsLast (compareExp pats e1 e2)
compareStmts pats s1 s2 = s1


compareExp' p [] [] = []
compareExp' p _ [] = []
compareExp' p [] _ = []
compareExp' p (e:es) (x:xs) = compareExp p e x : compareExp' p es xs

catPositions :: String -> [ String ]
catPositions [] = []
catPositions ('[':ps)
   = grabbed : catPositions ps'
      where
        (grabbed, ps') = (grabPositions ps, dropPositions ps)
        grabPositions [] = []
        grabPositions (']':xs) = []
        grabPositions ('<':'&':'>':ps)
          = ":" ++ grabPositions ps
        grabPositions (x:xs) = x : grabPositions xs

        dropPositions [] = []
        dropPositions (']':xs) = xs
        dropPositions (x:xs) = dropPositions xs


prunePositions :: String -> [String] -> [ [(SimpPos, SimpPos)] ]
prunePositions [] [] = []
prunePositions [] _  = []
prunePositions _ []  = []
prunePositions as (p:ps)
   = createSet as p : prunePositions remAnswers ps
    where
      remAnswers = drop ((length (filter (==':') p)) + 1) as

      createSet :: String -> String -> [ (SimpPos, SimpPos) ]
      createSet [] [] = []
      createSet [] _  = []
      createSet _  [] = []
      createSet ('y':xs) ps
         = ((read p2)::(SimpPos, SimpPos)) : createSet xs ps'
           where
             p2  = getPos ps
             ps' = dropPos ps
             getPos [] = []
             getPos (':':xs) = []
             getPos (x:xs)   = x : getPos xs

             dropPos [] = []
             dropPos (':':xs) = xs
             dropPos (x:xs)   = dropPos xs

      createSet ('n':xs) ps
         = createSet xs ps'
            where
             ps' = dropPos ps

             dropPos [] = []
             dropPos (':':xs) = xs
             dropPos (x:xs)   = dropPos xs

      createSet _ _ = []
