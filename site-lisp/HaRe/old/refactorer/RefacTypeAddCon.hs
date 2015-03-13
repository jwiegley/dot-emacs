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

module RefacTypeAddCon where
 
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
import RefacTypeUtils
import PFE0 (findFile)
import MUtils (( # ))
import RefacTypeLocUtils
-- import System
import System.IO
import TiDecorate

-- | An argument list for a function which of course is a list of paterns.
type FunctionPats = [HsPatP]

-- | A list of declarations used to represent a where or let clause.
type WhereDecls = [HsDeclP]


alphabet :: String
alphabet = "abcdefghijklmnopqrstuvwxyz"

refacTypeAddCon args
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
            (s, col', row', inf) <- doFileStuff fileName row col ans    
            modInfo2@(inscps', exps', mod', tokList') <- parseSourceFile (fileName ++ ".temp")
            -- Find the datatype that's been highlighted as the refactree
            let res = locToPN (fileName ++ ".temp") (row, col) mod'
            
            if res == defaultPN
              then do s <- AbstractIO.readFile (fileName ++ ".temp")
                      AbstractIO.writeFile fileName s
                      AbstractIO.removeFile (fileName ++ ".temp")
                      error "You must select the beginning of a constructor"
              else do   
                let decs = hsDecls mod'               
                let datDec = definingDecls [res] decs False True             
                -- get the list of constructors from the data type
                let datDec' = head datDec
                let datName = getDataName [datDec']
                let pnames = definedPNs datDec'
                -- ==================             
                let newPN = locToPN (fileName ++ ".temp") (row', col') mod'
                let newPNT = locToPNT (fileName ++ ".temp") (row', col') mod'
                -- ==================
                numParam <- getParams datDec' newPNT
                let oldPnames = filter (/= newPN) pnames
                let position = findPos 0 newPN pnames            
              --  newMod <- removeFromInts mod'
                
                                     
                ((_,m), (newToks, newMod)) <- applyRefac (addCon pnames newPN newPNT numParam oldPnames position inf datName (tail first)) (Just (inscps', exps', mod', tokList')) (fileName ++ ".temp")
 
                writeRefactoredFiles False [((fileName, m), (newToks, newMod))]              
                AbstractIO.removeFile (fileName ++ ".temp")                         
                AbstractIO.putStrLn "Completed.\n"      
         else do
            error "refacAddCon must take a new constructor and a list of arguments."

findPos _ _ [] = 0
findPos count newPn (x:xs)
 | newPn == x = count 
 | otherwise  = findPos (count + 1) newPn xs

getBeforePN _ _ [] = 0            
getBeforePN c newPN (x:xs)
  | newPN /= x = (c + 1) + (getBeforePN (c + 1)newPN xs)
  | otherwise = c      
            

createFun name (x:xs) newPN
 = TiDecorate.Dec ( HsPatBind loc0 (pNtoPat funPName) (HsBody (nameToExp ("error \"added " ++ (concat (map ( ++ " ") (x:xs))) ++ " to " ++ name ++ " \"") )) (Decs [] ([],[])) )
     where funPName= PN (UnQual ("added" ++ x)) (S loc0)

            
getParams (TiDecorate.Dec (HsDataDecl _ _ _ cons _)) newPNT
 = numParam cons
     where
      -- numParam :: (MonadPlus m) => [HsConDeclP] -> m Int
       numParam [] = return 0
       numParam (x@(HsConDecl _ _ _ pnt list):cs)
        | newPNT == pnt = do list' <- countCon x
                             return $ length list'
        | otherwise = do x <- numParam cs
                         return x
       numParam (x@(HsRecDecl _ _ _ pnt list):cs)
        | newPNT == pnt = do list' <- countCon' x
                             return $ length list'
        | otherwise = do x <- numParam cs
                         return x

       numParam _ = return 0
       
countCon :: (MonadPlus m, Term t) => t -> m [Int]  
countCon co
 = applyTU (full_tdTU (constTU [] `adhocTU` inCon)) co
    where
 --     inCon :: (Monad m) =>  HsTypeP -> m [Int]
      inCon a@(HsTyCon _::TI PNT (HsTypeI PNT)) = return [0]
      inCon _ = return []

countCon' :: (MonadPlus m, Term t) => t -> m [Int]
countCon' co
 = applyTU (full_tdTU (constTU [] `adhocTU` inCon)) co
    where
      inCon a@((x, _)::([PNT], HsBangType (HsTypeI PNT))) = return $ replicate (length x) 0
      inCon _ = return []      
       
addCon pnames newPn newPNT numParam oldPnames  position inf datName xs (inscps, exps, mod)
 = do
      newMod <- addDecl mod Nothing ([createFun datName xs newPn], Nothing) True
      res <- findFuncs newMod pnames newPn newPNT numParam oldPnames position datName inf xs
      
      return res 
          

 
findPosBefore newPN [] = []
findPosBefore newPN (x:[]) = [x]
findPosBefore newPN (x:y:ys)
 | newPN == y = [x]
 | otherwise  = findPosBefore newPN (y:ys)
 
            
findFuncs t pnames newPn newPNT numParam oldPnames position datName inf (x:xs)
  = applyTP (stop_tdTP ( failTP `adhocTP` inFun)) t
     where
      inFun dec1 
        = do
            (pat, exp1) <- findCase dec1
            -- error $ show dec1    
            if pat /= False
             then do 
                    let altPNs = getPNPats exp1
                    if oldPnames /= altPNs
                     then do
                      let posBefore = findPosBefore newPn pnames
                      update exp1 (newPat3 exp1 (head posBefore)) dec1
                --    update exp1 (newPat exp1) exp1    
                     else do
                      update exp1 (newPat2 exp1) dec1    
        
             else 
              do match <- findFun dec1
                 if match == False 
                   then do  --error "not found"
                       fail ""
                   else 
                     do  let funPNs = getPNs dec1
                 --      error $ show funPNs
                         if oldPnames /= funPNs 
                           then do
                            let posBefore = findPosBefore newPn pnames
                            if length posBefore > 1
                             then do
                              update dec1 (newMatch3 dec1 (head posBefore)) dec1
                             else do
                           --  error $ show posBefore
                              update dec1 (newMatch dec1) dec1
                           else do
                          -- error $ show position
                           update dec1 (newMatch2 dec1) dec1
                       where
                        newMatch (TiDecorate.Dec (HsFunBind loc1 matches@((HsMatch _ pnt _ e ds):ms))) 
                          =  TiDecorate.Dec (HsFunBind loc1 (newMatches matches pnt))  
                          
                        newMatch2 (TiDecorate.Dec (HsFunBind loc1 matches@((HsMatch _ pnt _ e ds):ms) ))
                          = TiDecorate.Dec (HsFunBind loc1 (fst ++ (newMatch' pnt) ++ snd) )
                            where 
                              (fst, snd) = splitAt position matches
                              
                        newMatch3 (TiDecorate.Dec (HsFunBind loc1 matches@((HsMatch _ pnt _ e ds):ms))) posBefore
                          = TiDecorate.Dec (HsFunBind loc1 (newMatches' matches pnt posBefore))
                                       
                                                                         
                        newMatches [] pnt = newMatch' pnt   
                        newMatches (m@(HsMatch _ _ pats _ _):ms) pnt
                         | or (map wildOrID pats) = (newMatch' pnt) ++ (m : ms)
                         | otherwise                     = m : (newMatches ms pnt)

                        newMatches' [] pnt posBefore = newMatch' pnt
                        newMatches' (m@(HsMatch _ _ pats _ _):ms) pnt posBefore
                         | (getPN pats) == posBefore = m : ((newMatch' pnt) ++ ms)
                         | or (map wildOrID pats) = (newMatch' pnt) ++ (m : ms)
      --                   | (TiDecorate.Pat HsPWildCard) `elem` pats = (newMatch' pnt) ++ (m : ms)
                         | otherwise      = m : (newMatches' ms pnt posBefore)                                       
                                       
                        newMatch' pnt 
                         | numParam == 0  =  [HsMatch loc0 pnt [pNtoPat newPn] (HsBody (nameToExp ("added" ++ x))) (Decs [] ([], []))]  
                         | otherwise = [HsMatch loc0 pnt [patt] (HsBody (nameToExp ("added" ++ x))) (Decs [] ([], []))]
                                        where
                                         patt 
                                          | inf == False = (TiDecorate.Pat (HsPParen (TiDecorate.Pat (HsPApp newPNT (createNames numParam ['a'..'z']))))::HsPatP)
                                          | otherwise    = (TiDecorate.Pat (HsPInfixApp (nameToPat "a") newPNT (nameToPat "b"))::HsPatP)
                                         createNames 0 _ = []
                                         createNames count (x:xs)
                                          = (nameToPat [x]) : (createNames (count-1) xs)
                                          
                        newPat (TiDecorate.Exp (HsCase e pats@((HsAlt loc p e2 ds):ps)))
                          = TiDecorate.Exp (HsCase e (newPats pats))
                     
                        newPat2 (TiDecorate.Exp (HsCase e pats))
                          = TiDecorate.Exp (HsCase e (fst ++ newPat' ++ snd))
                             where
                              (fst, snd) = splitAt position pats
                                       
 
                        newPat3 (TiDecorate.Exp (HsCase e pats)) posBefore
                          = TiDecorate.Exp (HsCase e (newPats' pats posBefore))
                     
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
                         | numParam == 0 = [HsAlt loc0 (pNtoPat newPn) (HsBody (nameToExp ("added" ++ x))) (Decs [] ([], []))]
                         | otherwise = [HsAlt loc0 patt (HsBody (nameToExp ("added" ++ x))) (Decs [] ([], []))]
                            where
                             patt 
                              | inf == False = (TiDecorate.Pat (HsPParen (TiDecorate.Pat (HsPApp newPNT  (createNames numParam ['a'..'z']))))::HsPatP)
                              | otherwise    = (TiDecorate.Pat (HsPInfixApp (nameToPat "a") newPNT (nameToPat "b"))::HsPatP)

                             createNames 0 _ = []
                             createNames count (x:xs)
                               = (nameToPat [x]) : (createNames (count-1) xs)

      --The selected sub-expression is in the argument list of a match
      --and the function only takes 1 parameter
      findFun dec@(TiDecorate.Dec (HsFunBind loc matches)::HsDeclP)
        =  return $ findMatch matches
           where findMatch match 
                   = fromMaybe (False)
                      (applyTU (once_tdTU (failTU `adhocTU` inMatch)) match)
                 inMatch (mat@(HsMatch loc1  pnt pats (HsBody e) ds)::HsMatchP)
                  = Just (checkTypes datName [mat])
                 inMatch x@(_) = Nothing

      findFun a@(_) = return False
   
      findCase dec@(TiDecorate.Dec (HsFunBind loc matches)::HsDeclP)
        = return $ findExp matches
           where findExp alt
                  = fromMaybe ((False, defaultExp))
                     (applyTU (once_tdTU (failTU `adhocTU` inExp)) alt)
                 inExp (exp@(TiDecorate.Exp e)::HsExpP)
                  = Just ((findPat e), exp)  
                 inExp _ = Nothing                       
                 findPat alt
                  = fromMaybe (False)
                     (applyTU (once_tdTU (failTU `adhocTU` inPat)) alt)
                 inPat (pat@(HsAlt loc p e ds)::HsAltP)
                  = Just (checkTypes datName [pat])
                 inPat _ = Nothing              
      findCase pat@(_) =  return (False, defaultExp)
                           
wildOrID (TiDecorate.Pat HsPWildCard) = True
wildOrID (TiDecorate.TiPSpec _ _ _ )    = True
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
                                
    AbstractIO.catch (AbstractIO.writeFile (fileName ++ ".temp") new)
                      (\_ -> do AbstractIO.removeFile (fileName ++ ".temp")
                                AbstractIO.writeFile (fileName ++ ".temp") new)
  --  AbstractIO.writeFile fileName new
    
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



                    

