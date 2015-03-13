-----------------------------------------------------------------------------
-- |
-- Module      :  RefacAddCon
-- Copyright   :  (c) Christopher Brown 2006
--
-- Maintainer  :  cmb21@kent.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- This module contains a transformation for HaRe.
-- Add a new constructor to a data type

-----------------------------------------------------------------------------

module RefacAddCon where
 
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
import RefacUtils hiding (getParams)
import PFE0 (findFile)
import MUtils (( # ))
import RefacLocUtils
--import System
import System.IO
import System.IO.Unsafe
import Data.Char

-- | An argument list for a function which of course is a list of paterns.
type FunctionPats = [HsPatP]

-- | A list of declarations used to represent a where or let clause.
type WhereDecls = [HsDeclP]


alphabet :: String
alphabet = "abcdefghijklmnopqrstuvwxyz"

refacAddCon args
  = do 
       let len = length args
       if len > 2 
         then do 
            let (first,sec) = splitAt ((length args)-2) args
            let fileName    = first!!0
                ans         = concat ( map ( ++ " ") (tail first))
                row         = read (sec!!0)::Int
                col         = read (sec!!1)::Int
            AbstractIO.putStrLn "refacAddCon"   
            
            -- let modName = convertModName modName1            -- Parse the input file.
            modInfo@(inscps, exps, mod, tokList) <- parseSourceFile (fileName)   
            let res1 = locToPNT fileName (row, col) mod
                res2 = locToPN fileName (row, col) mod
                decs = hsDecls mod
                datDec = definingDecls [res2] decs False True
                datName = (declToName (ghead "datName" datDec))
                datPNT = (declToPNT (ghead "datPNT" datDec))
                 
                 -- add any new type params...

            ((_,m), (newToks, newMod)) <- applyRefac (addField (ghead "applyRefac" datDec) datPNT datName res1 (drop 1 (tail first)) tokList) 
                                                     (Just (inscps, exps, mod, tokList)) fileName
       
            writeRefactoredFiles False [((fileName, m), (newToks, newMod))]
                
            (s, col', row', inf) <- doFileStuff fileName row col ans    
            modName1 <- fileNameToModName fileName 

            let modName = convertModName modName1            -- Parse the input file.
            modInfo@(inscps, exps, mod, tokList) <- parseSourceFile (fileName)              
            -- Find the datatype that's been highlighted as the refactree
            
            {- case checkCursor fileName row col mod of
              Left errMsg -> do AbstractIO.removeFile (fileName ++ ".temp.hs")
                                error errMsg
              Right dat ->
                do
                 
                -}
                
            let res' = locToPNT fileName (row, col) mod
                res = pNTtoPN res'   
                 -- Parse the input file.
            AbstractIO.putStrLn ("parsing ..." ++ fileName ++ ".temp.hs")
            modInfo2@(inscps', exps', mod', tokList') <- parseSourceFileOld (fileName ++ ".temp.hs") 
            AbstractIO.putStrLn "parsed."                                               
            let decs = hsDecls mod'
                -- datDec = definingDecls [res] decs False True                
                 -- get the list of constructors from the data type
                decs' = hsDecls mod
                datDec'' = definingDecls [res2] decs False True
                datDec' = ghead "datDec'" datDec'' 
                -- datName = getDataName [datDec']
                pnames = definedPNs datDec' 
                newPN = locToPN (fileName ++ ".temp.hs") (row', col') mod'
                newPNT = locToPNT (fileName ++ ".temp.hs") (row', col') mod'
            numParam <- getParams datDec' newPNT
            let oldPnames = filter (/= newPN) pnames
                position = findPos 0 newPN pnames
                
            ((_,m), (newToks, newMod)) <- applyRefac (addCon (fileName) datName pnames newPN newPNT numParam oldPnames position inf (tail first) modName) 
                                                                 (Just (inscps', exps', mod', tokList')) (fileName++"temp.hs")
            writeRefactoredFiles True [((fileName, m), (newToks, newMod))]           
            AbstractIO.removeFile (fileName ++ ".temp.hs")                         
            AbstractIO.putStrLn "Completed.\n"      
         else do
            error "refacAddCon must take a new constructor and a list of arguments."

addField datDec datPNT pnt fName fType tok (_, _, t)
 = do
      newMod <- addTypeVar datDec datPNT pnt fType tok t
      return newMod
      
addingField pnt fName fType t
 = applyTP (stop_tdTP (failTP `adhocTP` inDat)) t
    where
     inDat (dat@(HsConDecl s i c p types)::HsConDeclP)
       | p == pnt = do
                       r <- update dat (HsConDecl s i c p (newTypes types fType)) dat
                       return r
     inDat (dat@(HsRecDecl s i c p types)::HsConDeclP)
       | p == pnt = do
                      r <- update dat (HsRecDecl s i c p (newRecTypes types fName fType)) dat
                      return r    
     inDat _ = fail ""
     
     
     -- newRecTypes must check that the name is not already declared as a field name
     -- within that constructor.
     newRecTypes xs n []  = xs
     newRecTypes xs n (a:as) 
       | n `elem` (map pNTtoName (unFlattern xs)) = error "There is already a field declared with that name!"
       | otherwise =  ([nameToPNT n], (HsUnBangedType (Typ (HsTyCon (nameToPNT a))))) : (newRecTypes xs n as)

     unFlattern :: [([a],b)] -> [a]
     unFlattern [] = []
     unFlattern ((xs, y):xss) = xs ++ (unFlattern xss)
                                 

     newTypes xs [] = xs
     newTypes xs (a:as) = HsUnBangedType (Typ (HsTyCon (nameToPNT a))) : (newTypes xs as)   

addTypeVar datDec datName pnt fType toks t
 = applyTP (full_buTP (idTP `adhocTP` (inDatDeclaration datDec))) t
    where
      inDatDeclaration _ (dat@(Dec (HsDataDecl a b tp c d))::HsDeclP) 
        | (defineLoc datName == (defineLoc.typToPNT.(ghead "inDatDeclaration").flatternTApp) tp) &&
          checkIn fType tp 
          = update dat (Dec (HsDataDecl a b (createTypFunc ((typToPNT.(ghead "inDatDeclaration").flatternTApp) tp) 
                                              ( ((map nameToTyp fType') ++ (tail (flatternTApp tp))) )) c d)) dat
            
             where
              fType' = checkInOne2 tp [" "] fType
                                              
      inDatDeclaration (Dec (HsDataDecl _ _ tp _ _)) (dat@(Dec (HsTypeSig s is c t))::HsDeclP) 
        | (pNTtoName datName) `elem` (map (pNTtoName.typToPNT) (flatternTApp t) )
          = do
               
               let res = changeType t tp
               if res == t
                 then return dat
                 else update dat (Dec (HsTypeSig s is c res)) dat

      inDatDeclaration _ t = return t
      
      checkIn [] tp = True
      checkIn (fType:fTypes) tp = 
       (fType `elem` (map (pNTtoName.typToPNT) (flatternTApp tp))) == False &&
            isLower (ghead "checkIn" fType) || (checkIn fTypes tp)
      
      checkInOne t tp n [] = []
      checkInOne t tp n (f:fs) 
        | (f `elem` (map (pNTtoName.typToPNT) (flatternTApp tp))) &&
              isLower (ghead "checkInOne" f) = checkInOne t tp n fs
        | (f `elem` (map (pNTtoName.typToPNT) (flatternTApp t))) &&
              isLower (ghead "checkInOne" f)  = newName : checkInOne t tp (n ++ [newName]) fs
        | (f `elem` (map (pNTtoName.typToPNT) (flatternTApp t))) == False &&
             isLower (ghead "checkInOne" f) = f : (checkInOne t tp n fs)
        | otherwise = checkInOne t tp n fs

            where
              newName = (mkNewName f (n ++ (map (pNTtoName.typToPNT) (flatternTApp tp))) 1)
       
      checkInOne2 tp n [] = []
      checkInOne2 tp n (f:fs) 
        | (f `elem` (map (pNTtoName.typToPNT) (flatternTApp tp))) == False &&
             isLower (ghead "checkInOne" f) = f : (checkInOne2 tp n fs)
        | otherwise = checkInOne2 tp n fs 
       
        
      changeType :: HsTypeP -> HsTypeP -> HsTypeP
      changeType t@(Typ (HsTyFun t1 t2)) tp
            = (Typ (HsTyFun (changeType t1 tp) (changeType t2 tp)))   
      changeType t@(Typ (HsTyApp (Typ (HsTyCon p)) t2)) tp
        | (defineLoc datName) == (defineLoc p) && 
          checkIn fType t 
            = createTypFunc ((typToPNT.(ghead "inDatDeclaration").flatternTApp) t) 
                                              ( ((map nameToTyp fType') ++ (tail (flatternTApp t)))) 
             where
              fType' = checkInOne t tp [" "] fType
      changeType t@(Typ (HsTyApp t1 t2)) tp
            = (Typ (HsTyApp (changeType t1 tp) (changeType t2 tp)))
      
              -- fType'' = checkNames ftype' t
      changeType t@(Typ (HsTyCon p)) tp
        | (defineLoc datName) == (defineLoc p) && 
             checkIn fType t
               = createTypFunc ((typToPNT.(ghead "inDatDeclaration").flatternTApp) t) 
                                              ( ((map nameToTyp fType') ++ (tail (flatternTApp t))))
            where
              fType' = checkInOne t tp [" "] fType
      changeType t tp = t
      
      flatternTApp :: HsTypeP -> [HsTypeP]
      flatternTApp (Typ (HsTyFun t1 t2)) = flatternTApp t1 ++ flatternTApp t2
      flatternTApp (Typ (HsTyApp t1 t2)) = flatternTApp t1 ++ flatternTApp t2
      flatternTApp x = [x]   



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



isDefinedData [] _    = error "Please select the beginning of a constructor!"
isDefinedData ((Dec (HsDataDecl _ _ _ cs i)):ds) c2
 | c2 `myIn` cs = True
 | otherwise  = isDefinedData ds c2
     where
       myIn _ [] = False
       myIn pnt ((HsConDecl _ _ _ i _):cs)
         | pnt == i   = True
         | otherwise  = myIn pnt cs
       myIn pnt ((HsRecDecl _ _ _ i _):cs)
         | pnt == i   = True
         | otherwise  = myIn pnt cs

convertModName (PlainModule s) = s
convertModName m@(MainModule f) = modNameToStr m


findPos _ _ [] = 0
findPos count newPn (x:xs)
 | newPn == x = count 
 | otherwise  = findPos (count + 1) newPn xs

getBeforePN _ _ [] = 0            
getBeforePN c newPN (x:xs)
  | newPN /= x = (c + 1) + (getBeforePN (c + 1)newPN xs)
  | otherwise = c      
            
createFun (x:xs) newPN datName
 = Dec ( HsPatBind loc0 (pNtoPat funPName) (HsBody (nameToExp ("error \"added " ++ (concat (map ( ++ " ") (x:xs))) ++ "to " ++ datName ++ "\"") )) [] )
    where funPName= PN (UnQual ("added" ++ x)) (S loc0)

            
getParams (Dec (HsDataDecl _ _ _ cons _)) newPNT
 = numParam cons
     where
       numParam [] = return 0
       numParam (x@(HsConDecl _ _ _ pnt list):cs)
        | newPNT == pnt = do 
                             list' <- countCon x
                             return $ length list'
        | otherwise = do x <- numParam cs
                         return x
       numParam (x@(HsRecDecl _ _ _ pnt list):cs)
        | newPNT == pnt = do list' <- countCon' x
                             return $ length list'
        | otherwise = do x <- numParam cs
                         return x

       -- numParam _ = return 0
       
countCon :: (MonadPlus m, Term t) => t -> m [Int]  
countCon co
 = applyTU (full_tdTU (constTU [] `adhocTU` inCon)) co
    where
      inCon a@(HsTyCon _::TI PNT HsTypeP) = return [0]
      inCon a@(HsTyVar _::TI PNT HsTypeP) = return [0]
      inCon _ = return []

countCon' :: (MonadPlus m, Term t) => t -> m [Int]
countCon' co
 = applyTU (full_tdTU (constTU [] `adhocTU` inCon)) co
    where
      inCon a@((x, _)::([PNT], HsBangType HsTypeP)) = return $ replicate (length x) 0
      -- inCon _ = return []
      
       
addCon fileName datName pnames newPn newPNT numParam oldPnames  position inf xs modName (inscps, exps, mod)
 = do
      newMod <- addDecl mod Nothing ([createFun xs newPn datName], Nothing) True
      -- unsafePerformIO.putStrLn $ show newMod
      res <- findFuncs fileName datName newMod pnames newPn newPNT numParam oldPnames position inf xs modName
      
   --   res2 <- findPatterns ses datName res pnames newPn newPNT numParam oldPnames position inf xs
      
      return res
      
getPNs (Dec (HsFunBind _ (m:ms) ))
 = checkMatch (m:ms)
    where checkMatch [] = []
          checkMatch ((HsMatch _ _ (p:ps) _ _):ms)
            | (getPN p) /= defaultPN = (getPN p) : checkMatch ms
            | otherwise = checkMatch ms
            
getPNPats (Exp (HsCase e pats))
 = checkAlt pats
    where checkAlt [] = []
          checkAlt ((HsAlt loc p e2 ds):ps)
            | p /= (Pat HsPWildCard) = (getPN p) : checkAlt ps
            | otherwise = checkAlt ps 
            
getPN p 
 = fromMaybe (defaultPN)
             (applyTU (once_tdTU (failTU `adhocTU` inPat)) p)
             
    where
      inPat (pat::PName)
       = Just pat
      -- inPat _ = Nothing
 
findPosBefore newPN [] = []
findPosBefore newPN (x:[]) = [x]
findPosBefore newPN (x:y:ys)
 | newPN == y = [x]
 | otherwise  = findPosBefore newPN (y:ys)


findFuncs fileName datName t pnames newPn newPNT numParam oldPnames position inf (x:xs) modName
  =  applyTP (stop_tdTP (failTP `adhocTP` inFun)) t
    where
    inFun dec1 
        = do
            (pat, exp1) <- findCase dec1 modName
            if pat /= False
             then do 
                    let altPNs = getPNPats exp1
                    if oldPnames /= altPNs
                     then do
                      let posBefore = findPosBefore newPn pnames
                      update exp1 (newPat3 exp1 (head posBefore)) dec1
                     else do
                      update exp1 (newPat2 exp1) dec1    
        
             else 
              do ((match,arity), patar) <- findFun dec1 modName
                 if match == False 
                   then do  --error "not found"
                       fail ""
                   else 
                     do  let funPNs = getPNs dec1
                         if oldPnames /= funPNs 
                           then do
                            let posBefore = findPosBefore newPn pnames
                            if length posBefore > 1
                             then do
                              update dec1 (newMatch3 dec1 (head posBefore) arity patar) dec1
                             else do
                              update dec1 (newMatch dec1 arity patar) dec1
                           else do
                           update dec1 (newMatch2 dec1 arity patar) dec1
                       where
                        newMatch (Dec (HsFunBind loc1 matches@((HsMatch _ pnt p e ds):ms)))  arity patar
                          =  Dec (HsFunBind loc1 (newMatches matches pnt arity patar (length p)))  
                          
                        newMatch2 (Dec (HsFunBind loc1 matches@((HsMatch _ pnt p e ds):ms) )) arity patar
                          = Dec (HsFunBind loc1 (fst ++ (newMatch' pnt arity patar(length p)) ++ snd) )
                            where 
                              (fst, snd) = splitAt position matches
                              
                        newMatch3 (Dec (HsFunBind loc1 matches@((HsMatch _ pnt p e ds):ms))) posBefore arity patar
                          = Dec (HsFunBind loc1 (newMatches' matches pnt posBefore arity patar (length p)))
                                       
                                                                         
                        newMatches [] pnt position arity patar = newMatch' pnt position arity patar
                        newMatches (m@(HsMatch _ _ pats _ _):ms) pnt position arity patar
                         | or (map wildOrID pats) = (newMatch' pnt position arity patar) ++ (m : ms)
                         | otherwise                     = m : (newMatches ms pnt position arity patar)

                        newMatches' [] pnt posBefore position arity patar = newMatch' pnt position arity patar
                        newMatches' (m@(HsMatch _ _ pats _ _):ms) pnt posBefore position arity patar
                         | (getPN pats) == posBefore = m : ((newMatch' pnt position arity patar) ++ ms)
                         | or (map wildOrID pats) = (newMatch' pnt position arity patar) ++ (m : ms)
      --                   | (TiDecorate.Pat HsPWildCard) `elem` pats = (newMatch' pnt) ++ (m : ms)
                         | otherwise      = m : (newMatches' ms pnt posBefore position arity patar)                                       
                                       
                        newMatch' pnt arity  patar position
                  --       | numParam == 0  =  [HsMatch loc0 pnt [pNtoPat newPn] (HsBody (nameToExp ("added" ++ x))) []  ]
                          = createMatch arity ['a'..'z'] patar
                            where
                              createMatch arity alpha patar 
                               | elem 1 arity
                                   = (HsMatch loc0 pnt (createPat arity patar alpha) (HsBody (nameToExp ("added" ++ x))) []) : (createMatch (mutatearity arity) alpha patar)
                               | otherwise = []

                              mutatearity [] = []
                              mutatearity (x:xs) 
                               | x == 1 = 0 : xs
                               | otherwise = x : (mutatearity xs)

                              createPat [] _ alpha= []
                              createPat (x:xs) ((y,n):ys) alpha
                               | x == 1    =  newPatt' : (createPat (replicate (length xs) 0) ys ((res4')))
                               | elem 1 y  = (conApps n) : (createPat xs ys (res3))
                               | otherwise = (createNames 1 alpha) ++ (createPat xs ys (tail alpha))
                                  where
                                    (_, res2) = splitAt numParam alpha
                                    conApps n = conApp y alpha n
                                    (_, res3) = splitAt ((myLength (conApps n)) * numParam -1) alpha
                                    
                                    (_, res4') = splitAt ((myLength newPatt') ) alpha
                                    newPatt' = patt alpha
                                    
                                    patt alpha 
                                     | inf == False = (Pat (HsPParen (Pat (HsPApp newPNT (createNames numParam alpha))))::HsPatP)
                                     | otherwise    = (Pat (HsPInfixApp (nameToPat [alpha!!0]) newPNT (nameToPat [alpha!!1]))::HsPatP)
                                     
                                    conApp xs alpha name
                                      = (Pat (HsPParen (Pat (HsPApp (nameToPNT name) (createPats xs alpha)))))
                                      
                                    myLength (Pat (HsPParen (Pat (HsPApp _ xs)))) = length xs
                                    myLength _ = 0  
                                                                        
                                    
                                    createPats [] alpha = []  
                                    createPats (x:xs) alpha
                                     | x == 1 = newPatt : (createPats xs (res4))
                                     | otherwise = (createNames 1 alpha) ++ (createPats xs (tail alpha))
                                        where
                                         (_, res4) = splitAt ((myLength newPatt)) alpha
                                         newPatt = patt alpha
                                    
                                    createNames 0 _ = []
                                    createNames count (x:xs)
                                     = (nameToPat [x]) : (createNames (count-1) xs)
                                          
                        newPat (Exp (HsCase e pats@((HsAlt loc p e2 ds):ps)))
                          = Exp (HsCase e (newPats pats))
                     
                        newPat2 (Exp (HsCase e pats))
                          = Exp (HsCase e (fst ++ newPat' ++ snd))
                             where
                              (fst, snd) = splitAt position pats
                                       
 
                        newPat3 (Exp (HsCase e pats)) posBefore
                          = Exp (HsCase e (newPats' pats posBefore))
                     
                        newPats [] = newPat'
                        newPats(pa@(HsAlt _ p _ _):ps)
                         | wildOrID p = newPat' ++ (pa:ps)
                         | otherwise              = pa : (newPats ps)
                     
                        newPats' [] posBefore = newPat'
                        newPats' (pa@(HsAlt _ p _ _):ps) posBefore
                         | (getPN p) == posBefore = pa : (newPat' ++ ps)
                         | wildOrID p = newPat' ++ (pa:ps)
                         | otherwise = pa : (newPats' ps posBefore)

                     
                        newPat' 
                         | numParam == 0 = [HsAlt loc0 (pNtoPat newPn) (HsBody (nameToExp ("added" ++ x))) [] ]
                         | otherwise = [HsAlt loc0 patt (HsBody (nameToExp ("added" ++ x))) []]
                            where
                             patt 
                              | inf == False = (Pat (HsPParen (Pat (HsPApp newPNT  (createNames numParam ['a'..'z']))))::HsPatP)
                              | otherwise    = (Pat (HsPInfixApp (nameToPat "a") newPNT (nameToPat "b"))::HsPatP)

                             createNames 0 _ = []
                             createNames count (x:xs)
                               = (nameToPat [x]) : (createNames (count-1) xs)

      --The selected sub-expression is in the argument list of a match
      --and the function only takes 1 parameter
    findFun dec@(Dec (HsFunBind loc matches)::HsDeclP) modName
        =  return $ findMatch matches
           where findMatch match 
                   = fromMaybe ((False, []), [([], "")])
                      (applyTU (once_tdTU (failTU `adhocTU` inMatch)) match)
                 inMatch (mat@(HsMatch loc1  pnt pats (HsBody e) ds)::HsMatchP)
                  = do
                       let (_, y) = checkTypesInPat datName pats modName fileName
                      -- error $ show y
                           
                       Just ((checkTypes2 datName (pNTtoName pnt) modName fileName), y)
                 inMatch x@(_) = Nothing

    findFun a@(_) _ = return ((False, []), [([], "")])
      
    findCase dec@(Dec (HsFunBind loc matches)::HsDeclP) modName
        = return (findExp matches)
           where findExp alt
                  = fromMaybe ((False, defaultExp))
                     (applyTU (once_tdTU (failTU `adhocTU` inExp)) alt)
                 inExp (exp@(Exp e)::HsExpP)
                  = Just ((findPat e), exp)  
                  
                  where                      
                   findPat alt
                    = fromMaybe (False)
                      (applyTU (once_tdTU (failTU `adhocTU` inPat)) alt)
                   inPat (pat@(HsAlt loc (Pat (HsPId (HsCon p))) e ds)::HsAltP)
                     = (Just (checkTypes datName (pNTtoName p) modName fileName))
                   inPat e -- (pat@(HsAlt loc (Pat (HsPId (HsVar _))) e ds)::HsAltP)
                     = do
                         case exp of
                          Exp (HsCase (Exp (HsId (HsVar x))) alts)
                                                            -> do
                                                                 -- find where p is defined, and get the type
                                                                 let decs = hsDecls t
                                                                 -- error ( show (pNTtoPN x))
                                                                 let y = definingDecls [(pNTtoPN x)] decs False True
                                                                 -- error $ show y
                                                                 if length y /= 0
                                                                  then do 
                                                                   let b = definedPNs (head y)
                                                                   Just (checkTypes datName (pNtoName (head b)) modName fileName)
                                                                  else  Nothing
                          _ -> Nothing
                   -- inPat e = error (show e) -- Nothing   
                 -- inExp _ = Nothing           
    findCase pat@(_) _ =  return (False, defaultExp)
flatternPat :: HsPatP -> [HsPatP] 
flatternPat (Pat (HsPAsPat i p)) = flatternPat p
flatternPat (Pat (HsPApp i p)) = (Pat (HsPId (HsCon i))) : (concatMap flatternPat p)
flatternPat (Pat (HsPTuple _ p)) = p
flatternPat (Pat (HsPList _ p)) = p
flatternPat (Pat (HsPInfixApp p1 i p2)) = (flatternPat p1) ++ (flatternPat p2)
flatternPat (Pat (HsPParen p)) = flatternPat p
flatternPat p@(Pat (HsPId i)) = [p]
flatternPat p = [p] 

wildOrID (Pat HsPWildCard) = True
wildOrID (Pat (HsPId (HsVar x))) = True
wildOrID _ = False

doFileStuff fileName r c a = do
    s <- AbstractIO.readFile fileName
    
    -- get the first half of the file (up to point user has selected)
    let rev = reverse (returnHalf r c (1,1) s)
    let rest = returnSndHalf r c (1,1) s
    let str = parseIt rest a
    let str' = parseIt' rest a       
    let len = length (myDiff s str')    
    let (st, fin) = splitAt len s
    let new = st ++ str ++ fin   
    let extraCol = parseTick 0 str
    let (col, row) = getRowCol r c (1,1) st
          
    -- Check that the file does not already exist first         
    -- or else it will lead into strange errors...
    AbstractIO.catch (AbstractIO.writeFile (fileName ++ ".temp.hs") new)
                      (\_ -> do AbstractIO.removeFile (fileName ++ ".temp.hs")
                                AbstractIO.writeFile (fileName ++ ".temp.hs") new)
    
    if '`' `elem` a 
      then do return (new, col + extraCol, row, True)
      else do return (new, col + extraCol, row, False)
 
-- function to parse to see if user is placing contructor at the beginning or end of statement...   
-- if the user has selected a ' ' or a character
-- parse forwards (which is really backwards) until a '|' or a '=' character is found
parseTick _ [] = 3
parseTick count (x:xs)
 | x == '`' = count + 1
 | otherwise = parseTick (count+1) xs


myDiff :: String -> String -> String
myDiff [] _ = []
myDiff (y:ys) (x:xs) 
 | (y:ys) == (x:xs) = ""
 | otherwise = y : (myDiff ys (x:xs))
 
parseIt :: String -> String -> String
parseIt "" str = error "Please select a position on the right hand side of the data type."
parseIt (x:xs) str 
 | x == '\n' || x == '|' = " | " ++ str ++ " "
 | x /= '\n' || x /= '|' = parseIt xs str
 | otherwise            = " | " ++ str ++ " "
 
parseIt' :: String -> String -> String
parseIt' "" str = ""
parseIt' (x:xs) str
 | x == '\n' || x == '|' = (x:xs)
 | x /= '\n' || x /= '|' = parseIt' xs str
 | otherwise             = (x:xs)

                                 
-- perform some primitve parsing. We need to check where abouts the user wants
-- to add the data structure: 
-- a) if the it is at the beginning - we need to check that the
--    use has selected at the end of a "=" sign -- if this is the case append "|" to the end
--    of the user string;
-- b) if a "=" does not proceed the position - append a "|" to the end
--
-- we do not need to check for any other cases as Programatica will pick up the errors
-- (if the position of adding the constructor is invalid, for example.)

-- function to return the half of the file that comes before the user position
returnHalf r c (col, row) "" = ""
returnHalf r c (col, row) (x:xs) 
  | x == '\n' = if (r == row) && (c == col)   then [x]
                                              else x : (returnHalf r c (1, row+1) xs)
  | otherwise = if c == col && (r == row)     then [x]
                                              else x : (returnHalf r c (col+1, row) xs)
                                              
returnSndHalf r c (col, row) "" = ""
returnSndHalf r c (col, row) (x:xs) 
  | x == '\n' = if (r == row) && (c == col)   then xs
                                              else (returnSndHalf r c (1, row+1) xs)
  | otherwise = if c == col && (r == row)     then xs
                                              else (returnSndHalf r c (col+1, row) xs)                                       
                                           
getRowCol r c (col, row) "" = (col, row)
getRowCol r c (col, row) (x:xs) 
 | x == '\n' = getRowCol r c (1, row+1) xs
 | otherwise = getRowCol r c (col+1, row) xs


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
                  -> [HsConDeclP]  -- ^ A tuple of,
                     -- (the function name, the list of arguments,
                     -- the expression highlighted, any where\/let clauses
                     -- associated with the function).
                     
findDefNameAndExp toks beginPos endPos t
  = fromMaybe ([])
              (applyTU (once_tdTU (failTU `adhocTU` inData)) t)
    where
      --The selected sub-expression is the rhs of a data type
      inData (dat@(HsConDecl loc1 is con i xs)::HsConDeclP)
       = error (show res) 
            where 
               res = pNtoExp (pNTtoPN i)
      inData _ = Nothing



                    

