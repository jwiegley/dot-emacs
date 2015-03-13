-----------------------------------------------------------------------------
-- |
-- Module      :  RefacSlicTuple
-- Copyright   :  (c) Christopher Brown 2006
--
-- Maintainer  :  cmb21@kent.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- This module contains a transformation for HaRe.
-- Symoblic Evaluation on tuples.
-- creates functions which evaluate the expressions
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

module RefacSlicTuple where


import System.IO.Unsafe

import RefacTypeSyn
import RefacLocUtils
import Data.Char
import GHC.Unicode
import AbstractIO
import Data.Maybe
import Data.List
import RefacUtils
import RefacRedunDec
import SlicingUtils

data Patt = Match HsMatchP | MyPat HsDeclP | Def [Char] deriving Show

refacSlicTuple args
  = do let 
           fileName    = args!!0
           row         = read (args!!1)::Int
           col         = read (args!!2)::Int
           answer      = args!!3

       AbstractIO.putStrLn "refacTuple"

       -- Parse the input file.
       modName1 <- fileNameToModName fileName 

       let modName = modNameToStr modName1
       modInfo@(inscps, exps, mod, tokList) <- parseSourceFile fileName

       -- Find the function that's been highlighted as the refactree
       case checkCursor fileName row col mod of
         Left errMsg -> do error errMsg
         Right decl ->
           do
              -- get the RHS
              let (x@(listExp, rhs, wh, wh2, localDefs, p):xs) = getRHS fileName answer decl  (locToPNT fileName (row, col) mod) False []  modName  
                                                  
              let name = (locToPN fileName (row, col) mod)                      
              -- let newDecl2 = getNamesFromDecl decl   
                            
              let newDecl = map (getDeclInWhere decl) (map (\(a,b,c,d,e,f) -> (b)) (x:xs))
         
                                          
              let newAnswer = convertAnswer answer listExp
                                          
              -- error $ show (x:xs)               
              res <- myMapM f (newAnswer, (x:xs))
              let res2 = map (\(a,b,c) -> a) res
                            
              let local2 = makeBools res
              let names = makeNames res
              let sortedDecls0 = sortDecls ((concat res2), local2, names)
              let sortedDecls = map (\(a,b, c) -> a) sortedDecls0
              let local3 = map (\(a,b, c) -> b) sortedDecls0
              let names2 = map (\(a,b,c) -> c) sortedDecls0
              -- newSortedDecls <- matchPatterns sortedDecls newDecl
                                          
              replacedDecls <- replaceWithNew answer (locToPN fileName (row, col) mod) sortedDecls (length listExp)
              
              newReplacedDecls <- removeDeadPatterns answer replacedDecls names2 -- (getNameOfDec (head newDecl))
                            
              newReplacedDecls2 <- removeDeadTupleCase newReplacedDecls newReplacedDecls 
              
              newReplacedDecls3 <- dependencyAnalysis newReplacedDecls2 (head newDecl) newReplacedDecls2 names2
                                                                                                                
              newSortedDecls2 <- createDecl newReplacedDecls3 decl local3 0 newAnswer              
              let newSortedDecls3 = sortDecls (newSortedDecls2, local3, names2)
              
              let refactoredDecls = map (\(a,b, c) -> a) newSortedDecls3
                                          
              res2 <- applyRefac (addDecls refactoredDecls name) (Just (inscps, exps, mod, tokList)) fileName    
              
              
                            
              writeRefactoredFiles True [res2]
              (inscps2, exps2, mod2, tokList2) <- parseSourceFile fileName
              
              let newRefactoredDecls1 = hsDecls mod2
              
              -- AbstractIO.putStrLn $ show (map declToName refactoredDecls)
              
              let newRefactoredDecls2 = definingDecls (map (declToPName (map declToName refactoredDecls)) newRefactoredDecls1) newRefactoredDecls1 False False
              
              
              -- AbstractIO.putStrLn $ show newRefactoredDecls2
              

              
              sigs <- mapM (getSigAsString fileName modName) (map declToName newRefactoredDecls2)
              
              -- AbstractIO.putStrLn $ show sigs
              
              -- AbstractIO.putStrLn $ show (map declToName newRefactoredDecls2)
               
              -- AbstractIO.putStrLn $ show (map (declToPName (map declToName refactoredDecls)) newRefactoredDecls1) 
               
               
              res3 <- applyRefac (addTypes (dropWhile (\x -> x == defaultPN) (map (declToPName (map declToName refactoredDecls)) newRefactoredDecls1)) sigs) (Just (inscps2, exps2, mod2, tokList2)) fileName
              
              
              -- error $ show res3
              
              writeRefactoredFiles True [res3]
              
          {-    (inscps5, exps5, mod5, tokList5, ses5) <- parseSourceFile2 fileName modName

              
              (mod',((tokList'',modified),_))<-(doCommenting (dropWhile (\x -> x == defaultPN) (map (declToPName (map declToName refactoredDecls)) newRefactoredDecls1))) fileName mod5 tokList5
              
              
              writeRefactoredFiles True [((fileName, True), (tokList'', mod'))] -}
               
              where 
                f a l@((listExp:es), rhs, wh, wh2, localDefs, p1) -- (tok, m)
                     = do      
                         if (listExp:es) == []
                          then error "Please select a definition that returns a tuple!"
                          else 
                           if localDefs == False 
                            then do     
                              let (funRHS, funName, wher, pats) = simpleGetRHS decl (locToPNT fileName (row, col) mod)
                              decl <- forEach (listExp:es) rhs wh wh2 fileName 0 a (funName, p1) (inscps, exps, mod, tokList)
                              
                              return (decl, False, funName)
                            else do
                              let (begin, end) = getStartEndLoc tokList (get1Element listExp)
                              let blah@(loc, pnt, pats, exp, wh2, p)
                                    = findDefNameAndExp tokList
                                      begin
                                      end
                                      mod 
                              let (funRHS, funName, wher, pats) = simpleGetRHS decl (locToPNT fileName (row, col) mod)
                              decl <- forEach2 wher (listExp:es) rhs wh wh2 fileName 0 a (funName, p1) (inscps, exps, mod, tokList)
                              return (decl, True, pnt) 
                writeRefactored2 x = writeRefactoredFiles False [x]     
            
                myMapM f (a, [l])  
                  = do  
                        res <- f a l -- (tokList, mod)
                        return [res]
                        
                myMapM f (a , (l:list)) 
                  = do 
                       res <- f a l -- (tokList, mod)
                       x <- myMapM f (a ,list) -- (tokList, mod)   
                       return (res : x)  

convertModName (PlainModule s) = s
convertModName m@(MainModule f) = modNameToStr m


--createTypeSig :: String -> [String] -> [String] -> HsDeclP
createTypeSig name [] types 
 = Dec (HsTypeSig loc0 [nameToPNT name] [] (createApplication types)) 
createTypeSig name context types  
 = Dec (HsTypeSig loc0 [nameToPNT name] [(Typ (HsTyVar (nameToPNT context)))] (createApplication types)) 
 
 -- (Typ (HsTyVar (nameToTypePNT (head types))) ) )
 

nameToTypePNT :: String -> PNT 
nameToTypePNT id = (PNT (PN (UnQual id) (S loc0)) (Type (TypeInfo {defType = Nothing, constructors = [], fields = []})) (N (Just loc0)))


createApplication [var]
 = (Typ (HsTyVar (nameToTypePNT var)))
createApplication (var:vars)
 = createApplication' (Typ (HsTyVar (nameToTypePNT var))) vars
 
createApplication' x [y]
  = (Typ (HsTyFun x (Typ (HsTyVar (nameToTypePNT y)))))
createApplication' x (y:ys)
  = (createApplication' (Typ (HsTyFun x (Typ (HsTyVar (nameToTypePNT y))))) ys)
       
findType pnt t
  = applyTU (stop_tdTU (failTU `adhocTU` inSig)) t
      where
        inSig (dec@(Dec (HsTypeSig _ _ _ _))::HsDeclP)
          = do
               let res = definesTypeSig (pNTtoPN pnt) dec
               if res == True
                  then return [True]
                  else fail ""
          
        inSig _ = fail "" 
 
 
 
{- declToName :: HsDeclP -> String
declToName (Dec (HsFunBind _ ((HsMatch _ pnt _ _ _):xs)))  
 = pNTtoName pnt
declToName (Dec (HsPatBind _ pnt _ _)) = pNTtoName (patToPNT pnt) -}

{- declToPName ::  [ String  ] -> HsDeclP -> PName
declToPName [] _ = defaultPN
declToPName (name: names) d@(Dec (HsFunBind _ ((HsMatch _ pnt _ _ _):xs))) 
 | name == pNTtoName pnt = pNTtoPN pnt
 | otherwise = declToPName  names d
declToPName (name:names) d@(Dec (HsPatBind _ pnt _ _))  -- = pNTtoPN (patToPNT pnt)
 | name == pNTtoName (patToPNT pnt) = pNTtoPN (patToPNT pnt)
 | otherwise = declToPName  names d
declToPName _ _ = defaultPN
-}
{- getSig ses modName name 
 = do
      let types = getTypes name ses modName
      -- error $ show types
      let types1 = cleanTypes (tail types)

      let (context, l) = getContext (head types)
      let types2 = l : types1
   --   let context2 = init context
      let types3 = map (filter (/= '\n')) types2
      let newSig = createTypeSig name context types3
     -- error $ show newSig
      
      return newSig -}


makeBools :: [ ([HsDeclP], Bool, PNT) ] -> [Bool]
makeBools [] = []
makeBools (( x, False, _) : xs)
 = (replicate (length x) False) ++ (makeBools xs)
makeBools (( x, True, _) : xs)
 = (replicate  (length x) True) ++ ( makeBools xs )

makeNames :: [ ([HsDeclP], Bool, PNT) ] -> [PNT]
makeNames [] = []
makeNames (( x, _, y) : xs)
 = (replicate (length x) y) ++ (makeNames xs)



createDecl [] _ _ _ _ = return []
createDecl (d3@(Dec (HsFunBind _ (m@(HsMatch l i1 ps (HsBody e) ds):ms) )):ds3) t@(Dec (HsPatBind loc2 p2 (HsBody e2) ds2)) (True:xs) count a
 = do
      let (newCount, newAnswer) = countAnswer count a   
      result2 <- renamePN2 (getNameFromExp e2)  i1  e2
      let (jj,ii) = span (defines' (pNTtoPN i1)) (d3:ds3)
      newSortedDecls3 <- removeRedunWhere2 ((d3:ds3) ++ ds2) result2   
      rest <- createDecl (ii) t (drop (length jj) (True:xs)) newCount newAnswer
      return ((Dec (HsPatBind loc2 (nameToPat ((pNTtoName (patToPNT p2)) ++ (show newCount))) (HsBody result2) newSortedDecls3)) : rest)
createDecl (d3@(Dec (HsFunBind _ (m@(HsMatch l i1 ps (HsBody e) ds):ms) )):ds3) t@(Dec (HsFunBind loc (m2@(HsMatch l2 i2 ps2 (HsBody e2) ds2):ms2))) (True:xs) count a
 = do
      let (newCount, newAnswer) = countAnswer count a   
      result <- checkMatch (m2:ms2) i1 newCount
      let (jj,ii) = span (defines' (pNTtoPN i1)) (d3:ds3)
      rest <- createDecl (ii) t (drop (length jj) (True:xs)) newCount newAnswer
      return ( (Dec (HsFunBind loc result)) : rest )

       where
        checkMatch [] _ _ = return []
        checkMatch (m2@(HsMatch l2 i2 ps2 (HsBody e2) ds2):ms2) i1 newCount
         = do 
              if isPrefixOf (pNtoName (getNameFromExp e2)) (pNTtoName i1)
               then do
                result2 <- renamePN2 (getNameFromExp e2)  i1  e2
                newSortedDecls3 <- removeRedunWhere2 ((d3:ds3) ++ ds2) result2 
                rest2 <- checkMatch ms2 i1 newCount  
                return ((HsMatch l2 (nameToPNT ((pNTtoName i2) ++ (show newCount))) ps2 (HsBody result2) newSortedDecls3):rest2)
               else do
                result <- checkMatch ms2 i1 newCount
                return result
                
createDecl (d:ds) t (False:xs) c a = do
                                      rest <- createDecl ds t xs c a
                                      return (d : rest)
  
-- xcreateDecl _ _ [] _ = return []                                   
-- createDecl a x y z  = error $ show (a, x,y,z)                                     
                                     
renamePN2::  (Monad m, Term t) =>
               PName               -- ^ The identifier to be renamed.
             ->PNT                 -- ^ The new name 
             ->t                   -- ^ The syntax phrase
             ->m t  

renamePN2 oldPN  newName  t
  = applyTP (full_tdTP (adhocTP idTP rename)) t
  where
    rename  pnt@(PNT pn y z )
     | (pn ==oldPN) && (srcLoc oldPN == srcLoc pn)
     = return newName 
    --  where 
    --    replaceName = replaceNameInPN Nothing       
    rename x = return x 


getNameFromExp (Exp (HsApp e1 e2))
 = getNameFromExp e1
getNameFromExp e1
 = expToPN e1

                        
getNameOfDec :: HsDeclP -> PNT
getNameOfDec (Dec (HsFunBind loc ms))
 = getNameOfDecMatch ms
      where
        getNameOfDecMatch (m@(HsMatch l i1 ps (HsBody e) ds):ms)
          = i1

getNameOfDec (Dec (HsPatBind loc p (HsBody e) ds))
 = patToPNT p

getDeclInWhere :: HsDeclP -> HsExpP -> HsDeclP 
getDeclInWhere decl (Exp (HsApp e1 e2))
 = head ( findDef (expToPNT (e1)) decl )
getDeclInWhere decl _  = decl



mapNew (x@(listExp, rhs, wh, wh2, localDefs):xs)
 | localDefs == True = map (\(a,b,c,d,e) -> (a,b,c,d,True)) (x:xs)
 | otherwise = (x:xs)

convertAnswer [] ys = []
convertAnswer (x:xs) ys
 | x == 'a' || x == 'A' = replicate (length ys) 'x'
 | isDigit x = 'x' : (convertAnswer (nextXS xs) ys)
 | x == 'x' || x == 'X' = 'x' : (convertAnswer (nextXS xs) ys)
 | x == '_' = '_' : (convertAnswer (nextXS xs) ys)
 | otherwise = convertAnswer xs ys


matchPatterns [] _ = return []
matchPatterns (x:xs) (Dec (HsFunBind loc ms)) 
  =  do
        let len = length ms
        let ft = take len (x:xs)
        let result = correctPatterns ft ms
        result2 <- matchPatterns (drop len (x:xs)) (Dec (HsFunBind loc ms))
        return (result ++ result2)
matchPatterns (x:xs) (Dec (HsPatBind loc p (HsBody e) ds))
 = do
        return (x:xs)
 
correctPatterns [] _ = []
correctPatterns _ [] = []
correctPatterns ((Dec (HsFunBind loc0 ((HsMatch loc  pnt pats rhs ds):ms))):ds2) (m@(HsMatch _ _ pats2 _ _):ms2) 
 = ((Dec (HsFunBind loc0 ((HsMatch loc pnt pats2 rhs ds):ms))) : (correctPatterns ds2 ms2))
 

getLengthAnswer [] count = count
getLengthAnswer (x:xs) count
 = case x of
    '(' -> if (or (map isDigit xs)) then getLengthAnswer xs count
                                    else getLengthAnswer (tail (dropWhile (\x -> x /= ')') xs)) (count+1)
    ',' -> getLengthAnswer xs count
    '/' -> getLengthAnswer xs count
    'X' -> getLengthAnswer xs (count+1)
    'x' -> getLengthAnswer xs (count+1)   
    '_' -> getLengthAnswer xs (count+1)
    ')' -> count 
    _   -> if not (isDigit x) then error "Incorrect usage syntax" 
                              else maximum (map digitToInt (filter (isDigit) (x:xs)))                         

getLength1 "A" rhs = getLength2 rhs
getLength1 "a" rhs = getLength2 rhs
getLength1 _ _ = 0
              
getLength2 (rhs@(Exp (HsTuple x))) = length x
getLength2 _ = 0


shuffleRHS :: String -> [HsExpP] -> [HsExpP]
shuffleRHS _ [] = []
shuffleRHS [] _ = []
shuffleRHS ('x':xs) (y:ys) = y : (shuffleRHS xs ys)
shuffleRHS ('X':xs) (y:ys) = y : (shuffleRHS xs ys)
shuffleRHS ('_':xs) (y:ys) = shuffleRHS xs ys
shuffleRHS ('(':xs) (y:ys) 
  | or (map isDigit xs) = (Exp (HsTuple (shuffleRHS2 xs (y:ys)))) : (shuffleRHS (nextXS xs) (y:ys))
  | otherwise = (shuffleRHS xs (nestedTuples y)) ++ (shuffleRHS (nextXS xs) ys)
                  where
                   nestedTuples :: HsExpP -> [HsExpP]
                   nestedTuples (Exp (HsTuple ts)) = ts
                   nestedTuples e = error "The input string does not match the pattern of the RHS."
shuffleRHS (x:xs) (y:ys)
 | isDigit x = ((y:ys) !! ((digitToInt x)-1)) : ( shuffleRHS xs (y:ys))
 | otherwise = shuffleRHS xs (y:ys)

shuffleRHS2 (')':xs) (y:ys) = []
shuffleRHS2 (x:xs) (y:ys) 
 | isDigit x = ( (y:ys) !! ((digitToInt x)-1) ) : shuffleRHS2 xs (y:ys)
 | otherwise = shuffleRHS2 xs (y:ys)

nextXS [] = []
-- nextXS (')':xs) = [] 
nextXS ('/':xs) = xs  
nextXS (x:xs) = nextXS xs

addDecls (x:xs) id (_,_,mod) = do
                                mod' <- addDecl mod (Just id) ((x:xs),Nothing) True
                                return mod'


addTypes _ [] (_,_,mod) = return mod
addTypes (x:xs) (y:ys) (a,b,mod) = do

                                      -- mod' <- addTypeSigDecl mod (Just x) ([y], Nothing) True 
                                      
                                      let name = pNtoName x
                                      
                                      mod' <- insertComment (name ++ " :: " ++ y) x mod
                                      
                                      -- commentOutTypeSig x (y:ys)                                   
                                      res <- addTypes xs ys (a,b,mod')
                                      return mod'
                                      
commentThemOut (x:xs) (y:ys) = do
  commentOutTypeSig x (y:ys)
  
  
doCommenting (x:xs) fileName mod tokList 
    =  runStateT (applyTP ((once_tdTP (failTP `adhocTP` (rmInMod (x:xs) )
                                              ))) mod)
                                                         ((tokList,unmodified),fileName)
                       
           where          
             --1. The definition to be removed is one of the module's top level declarations.
             rmInMod [] mod = return mod
             rmInMod (p:ps) (mod@(HsModule loc name exps imps ds):: HsModuleP)  
                = do ds'<-commentOutTypeSig p ds
                     -- ds' <- 
                     res2 <- rmInMod ps (HsModule loc name exps imps ds')
                     return res2
             -- rmInMod _ _ =mzero  
  
{- removeDeadPatternsCase [] _ = return []
removeDeadPatternsCase (d@(Dec (HsFunBind loc ms)):ds) decs
 = do
      res <- removeDeadCaseArgs ms decs
      rest <- removeDeadPatternsCase ds decs
      return ((Dec (HsFunBind loc )):rest)
       where
        removeDeadCaseArgs [] _ = return []
        removeDeadCaseArgs _ [] = return []
        removeDeadCaseArgs (m@(HsMatch l i1 ps (HsBody e) ds):ms) d
         = do
              res <- removeDeadCaseArgs2 i1 ds d
              rest <- removeDeadCaseArgs ms d
              return ((HsMatch l i1 ps (HsBody e) res):rest)
              
        removeDeadCaseArgs2 _ [] _ = return []
        removeDeadCaseArgs2 pnt (d@(Dec (HsPatBind loc p (HsBody e) ds)):dss) decs
         = case p of
            (Pat (HsPTuple s (l:ls))) -> if returnRHS pnt e
                                           then do
                                             newRHS <- removeDeadTupleCase ds decs    
                                             return newRHS
                                           else do
                                            return (d:dss)
            p                         ->  -}


createNewRHS count (d:ds) pnt var params
     = do
         let result = res (findDec (d:ds) ((pNTtoName pnt) ++ (show count)) (pNTtoName pnt) (show count) var (d:ds) )
         return result
           where
                res (Dec (HsFunBind _ (m@(HsMatch l i1 ps (HsBody e) ds):ms))) = createFunc i1 params
                res (Dec (HsPatBind loc p _ _)) = pNtoExp (patToPN p)
                convertPNTs [] = []
                convertPNTs (pnt:pnts) = ((pNTtoName pnt) ++ (show count)) : (convertPNTs pnts)


findDec [] x fun var name list = error ( "The variable: " ++ name ++ " requires element " ++ 
                                 var ++ " from " ++ fun ++ ". Please retry slicing element " ++ var ++ " as well.")
findDec (d@(Dec (HsFunBind _ (m@(HsMatch l i1 ps (HsBody e) ds1):ms))):ds) name a b c list
   | (pNTtoName i1) == name = d
   | otherwise = findDec ds name a b c list
findDec (d@(Dec (HsPatBind loc p _ _)):ds) name a b c list
   | pNTtoName (patToPNT p) == name = d
   | otherwise = findDec ds name a b c list

{-|
	createFunc takes the function name and a list of expressions to be
	used in the call. createFunc then creates a function application
	based on the expressions in the second argument.

createFunc :: PNT -> [HsExpP] -> HsExpP
createFunc _ [] = defaultExp
createFunc pat [exp]
  = (Exp (HsApp (Exp (HsId (HsVar pat))) exp))
createFunc pat (exp:exps)
  = createFunc' (Exp (HsId (HsVar (pat)))) (exp:exps)

-- | createFunc' is used by createFunc to build up a function application
createFunc' :: HsExpP -> [HsExpP] -> HsExpP
createFunc' exp [x]
  = (Exp (HsApp exp x))
createFunc' exp (x:xs)
  = (createFunc' (Exp (HsApp (exp) x)) xs)

-}

 
dependencyAnalysis [] _ _ _ = return []
dependencyAnalysis (d@(Dec (HsFunBind loc ms)):ds) origDec decs (pnt:pnts)
	= do
		res <- fixDependency ms origDec decs (pnt:pnts)
		rest <- dependencyAnalysis ds origDec decs pnts
		return ((Dec (HsFunBind loc res)):rest)
			where
                fixDependency [] _ _ _ = return []
                fixDependency (m@(HsMatch l i1 ps (HsBody e) ds):ms) d decs (p:pns)
                  = do
                     res <- fixDependency2 p ds d decs
                     rest <- fixDependency ms d decs pns
                     return ((HsMatch l i1 ps (HsBody e) res):rest)

                
                fixDependency2 _ [] _ _ = return []
                fixDependency2 pnt d@((Dec (HsFunBind loc ms)):dss) decs allDecs
                 = do
                      rest <- fixDependency2 pnt dss decs allDecs
                      return ((Dec (HsFunBind loc ms)): rest)
                fixDependency2 pnt (d@(Dec (HsPatBind loc p (HsBody e) ds)):dss) decs allDecs
				 = case p of
				    (Pat (HsPTuple s (p1:ps1))) 
				       ->  if returnRHS pnt e
 				           then do
  				            rhs <- correctTupleRHS pnt (p1:ps1) dss decs allDecs e
 				            {- count <- correctRHS p1 decs   -}
 				            rest <- fixDependency2 pnt dss decs allDecs
 				            let rhs2 = case e of
 				                        (Exp (HsCase _ alts)) -> (Exp (HsCase (Exp (HsTuple rhs)) alts))
 				                        _                     -> (Exp (HsTuple rhs))
 				               
 				            return ((Dec (HsPatBind loc p (HsBody rhs2) ds)):rest)
 				           else do
 					         rest <- fixDependency2 pnt dss decs allDecs
 					         return ((Dec (HsPatBind loc p (HsBody e) ds)):rest)
				    _ ->  if returnRHS pnt e
				           then do
				            count <- correctRHS p decs 
				            if count /= 0
				              then do  
				                rest <- fixDependency2 pnt dss decs allDecs
				                let params = getParams pnt e 
				                newRHS <- createNewRHS count allDecs pnt (pNTtoName (patToPNT p)) params
				                return ((Dec (HsPatBind loc p (HsBody newRHS) ds)):rest)
				              else do
				                rest <- fixDependency2 pnt dss decs allDecs
				                return rest
				           else do
					         rest <- fixDependency2 pnt dss decs allDecs
					         return ((Dec (HsPatBind loc p (HsBody e) ds)):rest)
					         
					         
               	correctTupleRHS :: Monad m => PNT -> [HsPatP] -> [HsDeclP] -> HsDeclP -> [HsDeclP] -> HsExpP -> m [HsExpP]
                correctTupleRHS _ [] _ _ _ _ = return []	
                correctTupleRHS pnt (p:ps) dss decs allDecs e
                 = do
                     count <- correctRHS p decs
                     if count /=0 
                       then do
                         -- rest <- fixDependency2 pnt dss decs allDecs
                         let params = getParams pnt e 
                       --  error $ show (count, pnt, (pNTtoName (patToPNT p)))
                         newRHS <- createNewRHS count allDecs pnt (pNTtoName (patToPNT p)) params
                         rest <- correctTupleRHS pnt ps dss decs allDecs e
                         return ( newRHS : rest)		
				       else do
				         rest <- correctTupleRHS pnt ps dss decs allDecs e
				         return rest
				       
correctRHS :: Monad m => HsPatP -> HsDeclP -> m Int
correctRHS (Pat (HsPParen p)) origDec
  = do
		result <- correctRHS p origDec
		return result
correctRHS (Pat (HsPTuple _ (p:ps))) origDec
  = do
		result <- correctRHS p origDec
		return result
			
correctRHS (Pat (HsPId (HsVar (PNT (PN (UnQual x2) s) _ _)))) (Dec (HsFunBind loc ms))
  = do
		result <- correctRHS2 ms x2
		return result
correctRHS p d
 = return 0					
				
correctRHS2 [] _ = return 0
correctRHS2 (m@(HsMatch l i1 ps _ ds):ms) x2
 = do
      res  <- correctRHS3 i1 ds x2
      rest <- correctRHS2 ms x2
      if res /= 0
        then return res
        else return rest
 
correctRHS3 _ [] _ = return 0
correctRHS3 pnt (d@(Dec (HsPatBind loc p (HsBody e) ds)):dss) x2
	= if returnRHS pnt e
		then do
			-- which element is x2 contained within p?
			count <- countPat [p] x2 1
			return count
		else do
			rest <- correctRHS3 pnt dss x2
			return rest
correctRHS3 pnt (d@(Dec (HsFunBind loc ms)):dss) x2
    = do
         matches <- checkMatches ms x2
         if matches /= 0 
           then return matches
           else do
                  res <- correctRHS3 pnt dss x2
                  return res
         where
           checkMatches [] _ = return 0
           checkMatches (m@(HsMatch l i1 ps (HsBody e) ds):ms) x2
            = do
                  res  <- correctRHS3 i1 ds x2
                  rest <- correctRHS2 ms x2
                  if res /= 0
                   then return res
                   else return rest
															
{-}	correctRHS3 (d:dss) x2 = do rest <- correctRHS3 dss x2 
							                         return 0 -}
						
countPat :: Monad m => [HsPatP] -> String -> Int -> m Int
countPat  [] x count = return count
countPat [Pat (HsPTuple _ (p:ps))] x2 count
 = do
       let result = inPat [p] x2
       if result then return count
                 else do result2 <- countPat ps x2 (count+1)
                         return result2
countPat  ((Pat (HsPTuple _ (p:ps))):ps2) x2 count
 = do
		let result = inPat (p:ps) x2
		if result then return count
                  else do result2 <- countPat ps2 x2 (count + 1)
                          return result2
countPat (p:ps) x2 count
 = do
       let result = inPat [p] x2
       if result then return count
                 else do result2 <- countPat ps x2 (count+1)		
                         return result2	
                         		
inPat [] _ = False	
inPat ((Pat (HsPId (HsVar (PNT (PN (UnQual x1) s) _ _)))):ps) x2
	| x1 == x2 = True
	| otherwise = inPat ps x2	     
inPat ((Pat (HsPTuple _ (p:ps))):ps2) x2
	| inPat (p:ps) x2 = True
	| otherwise = inPat ps2 x2 
inPat ((Pat (HsPParen p)):ps) x2
 = inPat (p:ps) x2
inPat (p:ps) x2
	= inPat ps x2
						            
           

removeDeadTupleCase [] _ = return []
removeDeadTupleCase (d@(Dec (HsFunBind loc ms)):ds) decs
 = do
      res <- removeDeadCaseArgs ms decs
      rest <- removeDeadTupleCase ds decs
      return ((Dec (HsFunBind loc res)):rest)
       where
        removeDeadCaseArgs [] _ = return []
        removeDeadCaseArgs _ [] = return []
        removeDeadCaseArgs (m@(HsMatch l i1 ps (HsBody e) ds):ms) d
         = do
              res <- removeDeadCaseArgs2 i1 ds d
              rest <- removeDeadCaseArgs ms d
              return ((HsMatch l i1 ps (HsBody e) res):rest)

        removeDeadCaseArgs2 _ [] _ = return []
        removeDeadCaseArgs2 pnt (d@(Dec (HsPatBind loc p (HsBody e) ds)):dss) decs
         = case p of
            (Pat (HsPTuple s (l:ls))) -> if returnRHS pnt e
                                           then do
                                             newRHS <- removeDeadTupleCase2 (l:ls) decs [e]   
                                             rest <- removeDeadCaseArgs2 pnt dss decs
                                             if length newRHS == 1
                                                then do
                                                  let newRHS1 = newRHS !! 0
                                                  return ((Dec (HsPatBind loc p (HsBody newRHS1) ds)):rest)
                                                else do
                                                  return ((Dec (HsPatBind loc p (HsBody (Exp (HsTuple newRHS))) ds)):rest)
                                           else do
                                                rest <- removeDeadCaseArgs2 pnt dss decs
                                                return (d:rest)
            _                         -> if returnRHS pnt e
                                           then do
                                             newRHS <- removeDeadTupleCase2 [p] decs [e]
                                                                                          
                                             rest <- removeDeadCaseArgs2 pnt dss decs
   
                                             if length newRHS == 1
                                                then do
                                                  let newRHS1 = newRHS !! 0
                                                  return ((Dec (HsPatBind loc p (HsBody newRHS1) ds)):rest)
                                                else do
                                                  return ((Dec (HsPatBind loc p (HsBody (Exp (HsTuple newRHS))) ds)):rest)
                                           else do 
                                                   rest <- removeDeadCaseArgs2 pnt dss decs
                                                   return (d:rest)
        removeDeadCaseArgs2 pnt (d:dss) decs = do rest <- removeDeadCaseArgs2 pnt dss decs
                                                  return (d:rest)

                                            
        removeDeadTupleCase2 pats decs [(Exp (HsCase e1 alts ))]
               = do
                  newExp <- removeFromExp [e1] pats decs
                  return [(Exp (HsCase newExp alts))]
                  
        removeDeadTupleCase2 pats decs [e]
               = do 
                    newExp <- removeFromExp [e] pats decs
                    return [e]
                              
                  
        -- removeDeadTupleCase2 pats decs [e] = return [e]
           
        removeFromExp [(Exp (HsTuple (e:es)))] [p@(Pat (HsPId (HsVar (PNT (PN (UnQual x2) s) _ _))))] (d:ds)
           = do
               -- error $ show (d:ds)
               let dec = head (findDec e (d:ds) )
               -- error $ show (x2, dec, [p])
               if defines2 (PN (UnQual x2) s) [p] dec
                then do
                  -- error $ show e
                  return e  
                else do
                  -- error $ show (defines2 (PN (UnQual x2) s) [p] dec)
                  rest <- removeFromExp2 es [p] (d:ds)
                  return (Exp (HsTuple rest))
                           
        removeFromExp [(Exp (HsTuple (e:es)))] (p@(Pat (HsPId (HsVar (PNT (PN (UnQual x2) s) _ _)))):ps) (d:ds)
                     = do
                         let dec = head (findDec e (d:ds) )
                         -- check there is a wildcard. If there is we need to find the definition which defines
                         -- the names and the wildcard replacment
                         
                         -- error $ show dec
                         let pns = defines3 (PN (UnQual x2) s) (p:ps) dec
                         if defaultPN `elem` pns
                          then do
                            rest <- removeFromExp2 es (p:ps) (d:ds)
                            return (Exp (HsTuple rest)) 
                          else do     
                            -- error $ show (x2, dec)
                           if and (map ( (\a b c d -> a d b c)  defines2 (p:ps) dec) (hsPNs (p:ps)))
                            then do
                             rest <- removeFromExp2 es ps (d:ds)
                             return (Exp (HsTuple (e:rest)))
                         
                       {-  if defines2 (PN (UnQual x2) s) dec
                          then do
                           rest <- removeFromExp2 es ps (d:ds) 
                           return (Exp (HsTuple (e:rest)))   -}
                            else do
                             rest <- removeFromExp2 es ps (d:ds)
                             return (Exp (HsTuple rest))
        removeFromExp [e] _ _ = return e
                           
        removeFromExp2 [] _ _ = return []   
        removeFromExp2 (e@(Exp _):es) [p@(Pat (HsPId (HsVar (PNT (PN (UnQual x2) s) _ _))))] (d:ds)
                     = do
                          let dec = head (findDec e (d:ds) )
                          if defines2 (PN (UnQual x2) s) [p] dec
                           then do
                            -- error $ show (x2, dec)
                            return [e]   
                           else do
                            res <- removeFromExp2 es [p] (d:ds)
                            return res
        removeFromExp2 (e@(Exp _):es) (p@(Pat (HsPId (HsVar (PNT (PN (UnQual x2) s) _ _)))):ps) (d:ds)
                     = do
                          let dec = head (findDec e (d:ds) )
                          if defines2 (PN (UnQual x2) s) (p:ps) dec
                           then do
                            -- error $ show (x2, dec)
                            rest <- removeFromExp2 es ps (d:ds)
                            return (e:rest)   
                           else do
                            rest <- removeFromExp2 es ps (d:ds)
                            return rest
        removeFromExp2 a b c = return []
                    
                    
        findDec _ [] = error "this wasn't supposed to happen"
        findDec e@(Exp (HsApp (Exp (HsId (HsVar (PNT (PN (UnQual x) s) _ _ )))) e2)) (d:ds)
                     | inDec x d = [d]
                     | otherwise = findDec e ds
                     
                     
        inDec x (Dec (HsPatBind loc (Pat (HsPId (HsVar (PNT (PN (UnQual x2) s) _ _)))) (HsBody e) ds))
                     | x == x2 = True
                     | otherwise = False
        inDec x (Dec (HsFunBind _ ((HsMatch _ (PNT (PN (UnQual x2) s)_ _) _ _ _):ms)))
                     | x == x2 = True
                     | otherwise = False
        inDec _ _ = False

{- removeDeadPatterns _ [] _ = return []
removeDeadPatterns a ((Dec (HsFunBind loc ms)):ds) pnt
       = do
           res <- removeDeadPats ms pnt
           -- error $ show ds
           rest <- removeDeadPatterns a ds pnt
           return ((Dec (HsFunBind loc res)): rest)
            where
             removeDeadPats [] pnt = return []
             removeDeadPats (m@(HsMatch l i1 ps (HsBody e) ds):ms) pnt
              = do
                   (dec, free) <- hsFreeAndDeclaredPNs e
                   -- error $ show dec
                   res <- removeDeadPats2 a dec i1 ds
                   rest <- removeDeadPats ms pnt
                   return ((HsMatch l i1 ps (HsBody e) res):rest) 
                   
             removeDeadPats2 a dec pnt [] = return []
             removeDeadPats2 a dec pnt (d@(Dec (HsPatBind loc p (HsBody e) ds)):dss)
              = case p of
                  (Pat (HsPTuple s (l:ls))) -> if returnRHS2 pnt e
                                                  then do
                                                   newPats <- removeDeadPats3' s dec (l:ls)
                                                   newRHS <- removeDeadTupleEl pnt dec (l:ls) [e]
                                                   rest <- removeDeadPats2 a dec pnt dss
                                                   if length newRHS == 1
                                                     then do
                                                      let newRHS1 = newRHS !! 0
                                                      return ((Dec (HsPatBind loc newPats (HsBody newRHS1) ds)):rest)
                                                     else do
                                                      if length newRHS == 0
                                                       then error "There is an error with the variable dependency analysis!"
                                                       else
                                                        return ((Dec (HsPatBind loc newPats (HsBody (Exp (HsTuple newRHS))) ds)):rest)
                                                  else do
                                                   rest <- removeDeadPats2 a dec pnt dss
                                                   return ((Dec (HsPatBind loc p (HsBody e) ds)):rest)
                  _                          -> do
                                                  rest <- removeDeadPats2 a dec pnt dss
                                                  return (d:rest)
             removeDeadPats2 a dec pnt x = return x -}

removeDeadPatterns a ((Dec (HsFunBind loc ms)):ds) (pnt:pnts)
       = do
           res <- removeDeadPats ms pnt
           rest <- removeDeadPatterns a ds pnts
           return ((Dec (HsFunBind loc res)): rest)
            where
             removeDeadPats [] pnt = return []
             removeDeadPats (m@(HsMatch l i1 ps (HsBody e) ds):ms) pnt
              = do
                   (dec, free) <- hsFreeAndDeclaredPNs e
                   -- error $ show dec
                   res <- removeDeadPats2 a dec pnt ds
                   rest <- removeDeadPats ms pnt
                   return ((HsMatch l i1 ps (HsBody e) res):rest) 
                   
             removeDeadPats2 a dec pnt [] = return []
             removeDeadPats2 a dec pnt (d@(Dec (HsPatBind loc p (HsBody e) ds)):dss)
              = case p of
                  (Pat (HsPTuple s (l:ls))) -> if returnRHS pnt e
                                                  then do
                                                   newPats <- removeDeadPats3' s dec (l:ls)
                                                   newRHS <- removeDeadTupleEl pnt dec (l:ls) [e]
                                                   rest <- removeDeadPats2 a dec pnt dss
                                                   if length newRHS == 1
                                                     then do
                                                      let newRHS1 = newRHS !! 0
                                                      return ((Dec (HsPatBind loc newPats (HsBody newRHS1) ds)):rest)
                                                     else do
                                                      if length newRHS == 0
                                                       then error "There is an error with the variable dependency analysis!"
                                                       else
                                                        return ((Dec (HsPatBind loc newPats (HsBody (Exp (HsTuple newRHS))) ds)):rest)
                                                  else do
                                                   error $ show (pnt, e)
                                                   rest <- removeDeadPats2 a dec pnt dss
                                                   return ((Dec (HsPatBind loc p (HsBody e) ds)):rest)
                  _                          -> do
                                                  rest <- removeDeadPats2 a dec pnt dss
                                                  return (d:rest)
             removeDeadPats2 a dec pnt x = return x

             -- removeDeadPats3 [] _ = []
             removeDeadPats3' s a b
              = do
                   let res = removeDeadPats3 a b
                   if length res == 1
                    then do
                      let newRes = res !! 0
                      return newRes
                    else do
                      if res == []
                        then error "there is a problem with the dependency analysis on the RHS"
                        else return (Pat (HsPTuple s res))
             
             removeDeadPats3 :: [PName] -> [HsPatP] -> [HsPatP]
             removeDeadPats3 [] _ = []
             removeDeadPats3 _ [] = []
             removeDeadPats3 (x@(PN(UnQual x1) _):xs) (p@(Pat (HsPId (HsVar (PNT (PN (UnQual x2)_) _ _)))):ps)
               | myElem p (x:xs) = p : (removeDeadPats3 (x:xs) ps)
            --   | x1 == x2  = p : (removeDeadPats3 xs ps)
               | otherwise = removeDeadPats3 (x:xs) ps
             removeDeadPats3 (x@(PN(UnQual x1) _):xs) (p@(Pat (HsPTuple s (p1:ps))):pss)
                | allBlank (removeDeadPats3Tuple (x:xs) (p1:ps))   = removeDeadPats3 (x:xs) pss
                | otherwise = (Pat (HsPTuple s (removeDeadPats3Tuple (x:xs) (p1:ps)))) : (removeDeadPats3 (x:xs) pss)
                    where
                     allBlank ps = and (allBlank2 ps)
                     allBlank2 [] = [True]
                     allBlank2 ((Pat (HsPWildCard)):ps)
                      = True : (allBlank2 ps)
                     allBlank2 (p:ps)
                      = False : (allBlank2 ps)
                    
                     removeDeadPats3Tuple [] _ = []
                     removeDeadPats3Tuple _ [] = []
                     removeDeadPats3Tuple (x@(PN(UnQual x1) _):xs) (p@(Pat (HsPId (HsVar (PNT (PN (UnQual x2)_) _ _)))):ps)
                      | myElem p (x:xs) = p : (removeDeadPats3Tuple (x:xs) ps)
                      | otherwise =  (Pat (HsPWildCard)) : ( removeDeadPats3Tuple (x:xs) ps )   
                     removeDeadPats3Tuple a (p:ps)
                      = p : (removeDeadPats3Tuple a ps  )               
             -- pattern is either a wildcard or a literal
             removeDeadPats3 a  (p:ps) -- = error $ show p
               = removeDeadPats3 a ps
            -- removeDeadPats3 a b = error $ show b
               
               
               
             myElem :: HsPatP -> [PName] -> Bool
             myElem _ [] = False
             myElem a@(Pat (HsPParen p1)) (p:ps) = myElem p1 (p:ps)
             myElem a@(Pat (HsPId (HsVar (PNT (PN (UnQual x1)_) _ _)))) (p@(PN (UnQual x2) _):ps)
              | x1 == x2 = True
              | otherwise = myElem a ps
               
             removeDeadPats4' s a b c
              = do
                   let res = removeDeadPats4 a b c
                   if length res == 1
                    then do
                      let newRes = res !! 0
                      return newRes
                    else do
                      if res == []
                        then error $ show "blah"
                        else return (Pat (HsPTuple s res))
  
             removeDeadPats4 [] _ _ = []
             removeDeadPats4 _ [] _ = []
             removeDeadPats4 _ _ [] = []
             removeDeadPats4 (x@(PN(UnQual x1) _):xs) (p@(Pat (HsPParen p1)):ps)  (l:ls)
               = removeDeadPats4 (x:xs) (p1:ps) (l:ls)
             removeDeadPats4 (x@(PN(UnQual x1) _):xs) (p@(Pat (HsPTuple s (p1:ps1))):ps) (l:ls)
               | or (map (flip myElem (x:xs)) (p1:ps1)) = l : (removeDeadPats4 (x:xs) ps ls)
               | otherwise = removeDeadPats4 (x:xs) ps ls
             removeDeadPats4 (x@(PN(UnQual x1) _):xs) (p@(Pat (HsPId (HsVar (PNT (PN (UnQual x2)_) _ _)))):ps) (l:ls)
               | myElem p (x:xs) = l : (removeDeadPats4 (x:xs) ps ls)
               | otherwise = removeDeadPats4 (x:xs) ps ls
            -- removeDeadPats4 a b c =  error $ show (a,b,c)
             
             removeDeadTupleEl _ [] _ _ = return []
             removeDeadTupleEl _ _ [] _ = return []
             removeDeadTupleEl _ _ _ [] = return [] 
             removeDeadTupleEl pnt (x@(PN(UnQual x1) _):xs) (p@(Pat (HsPId (HsVar (PNT (PN (UnQual x2)_) _ _)))):ps) e1@[(Exp (HsTuple (e:es)))]
               = return e1
          --     | x1 == x2   = do
          {-     | myElem p (x:xs) = do
                                  res <- removeDeadTupleEl pnt (x:xs) ps es
                                  return (e : res)
               | otherwise  = do res <-  removeDeadTupleEl pnt (x:xs) ps es
                                 return res
                                 -}
                                 
             removeDeadTupleEl p a b [(Exp (HsIf e1 e2 e3))]
              = do
                   -- e1' <- removeDeadTupleEl' a b [e1]
                   e2' <- removeDeadTupleEl' p a b [e2]
                   e3' <- removeDeadTupleEl' p a b [e3]
                   return [(Exp (HsIf e1 e2' e3'))] 
                    
                                        
                                 
             removeDeadTupleEl pnt a b [(Exp (HsCase e1 (al:als) ))]
               = do
                  result <- removeDeadAlts (al:als) 
                  return [(Exp (HsCase e1 result))]
                   where
                    removeDeadAlts [] = return []
                    removeDeadAlts ((HsAlt s p (HsBody e) ds):as)
                     = 
                      case p of
                      (Pat (HsPTuple s2 (l:ls))) ->
                       do
                         if returnRHS pnt e1 && (length (l:ls) == length b)
                           then do
                            newPats <- removeDeadPats4' s2 a b (l:ls)
                            let res = removeDeadCase a b [e]
                            rest <- removeDeadAlts as
                            return ((HsAlt s newPats (HsBody (Exp (HsTuple res))) ds):rest)
                           else do
                            let res = removeDeadCase a b [e]
                            rest <- removeDeadAlts as
                            return ((HsAlt s p (HsBody (Exp (HsTuple res))) ds):rest)
                      _ ->
                       do    
                         let res = removeDeadCase a b [e]
                         rest <- removeDeadAlts as
                         return ((HsAlt s p (HsBody (Exp (HsTuple res))) ds):rest)                  
          --     | x1 == x2   = e : (removeDeadTupleEl xs ps es)
          --     | otherwise  = removeDeadTupleEl (x:xs) ps es
             removeDeadTupleEl pnt (x@(PN(UnQual x1) _):xs) (p@(Pat (HsPId (HsVar (PNT (PN (UnQual x2)_) _ _)))):ps) (e:es)
              = return (e:es)
          {-     | myElem p (x:xs) = do
                                  res <- removeDeadTupleEl pnt (x:xs) ps es
                                  return (e : res)
               | otherwise  = do res <-  removeDeadTupleEl pnt (x:xs) ps es
                                 return res  
                                 
                                 -}        
             removeDeadTupleEl _ _ _ x = return x
             
             removeDeadTupleEl' p a b e
               = do
                    res <- removeDeadTupleEl p a b e
                    if length res == 1
                      then do
                        let newRes = res !! 0
                        return newRes
                      else return (Exp (HsTuple res))

             removeDeadCase [] _ _ = []
             removeDeadCase _ [] _ = []
             removeDeadCase _ _ [] = []
             removeDeadCase (x@(PN(UnQual x1) _):xs) (p@(Pat (HsPId (HsVar (PNT (PN (UnQual x2)_) _ _)))):ps) [(Exp(HsTuple (e:es)))]
                | myElem p (x:xs) = e : (removeDeadCase (x:xs) ps es)
                | otherwise = removeDeadCase (x:xs) ps es
             removeDeadCase (x@(PN(UnQual x1) _):xs) (p@(Pat (HsPId (HsVar (PNT (PN (UnQual x2)_) _ _)))):ps) (e:es)
                | myElem p (x:xs) = e : (removeDeadCase (x:xs) ps es)
                | otherwise = removeDeadCase (x:xs) ps es
             removeDeadCase _ _ e = e  


-- return (d:dss) 
removeDeadPatterns a d _ = return d


                          

replaceWithNew a name [] _ = return []
replaceWithNew a name (d@(Dec (HsFunBind loc ms)):dss) total
 = do
      newMatches <- replaceInMatch ms total
      rest <- replaceWithNew a name dss total
      return ((Dec (HsFunBind loc newMatches)) : rest) 
  where
   replaceInMatch [] _ = return []
   replaceInMatch (m@(HsMatch l i1 ps (HsBody e) ds):ms) total
    = do
        newExp <- replaceInE a name total e
        let newExp2 = cleanNew newExp
        rest2' <- replaceWithNew a name ds total
        rest' <- replaceInMatch ms total
        return ((HsMatch l i1 ps (HsBody newExp2) rest2') : rest')
        
replaceWithNew a name (d@(Dec (HsPatBind loc p (HsBody e) ds)):dss) total
 = do
      newExp <- replaceInE a name total e
      let newExp2 = cleanNew newExp
      rest <- replaceWithNew a name ds total
      rest2 <- replaceWithNew a name dss total
      return ((Dec (HsPatBind loc p (HsBody newExp2) rest)): rest2)
      
cleanNew :: HsExpP -> HsExpP
cleanNew e@(Exp (HsTuple l))
 | length l == 1 = head l
 | otherwise     = e      
cleanNew e = e     
        
removeName (Exp (HsApp e1 e2))
 | removeName e1 == defaultExp = (Exp (HsApp defaultExp e2))
 | otherwise =  (Exp (HsApp (removeName e1) e2))    
removeName  e = defaultExp  
    
     
replaceInE a name total e
  = applyTP (once_tdTP (adhocTP idTP (rename' a))) e
     where
        rename' a e'@(Exp (HsApp e1 e2)::HsExpP)
         -- | a /= "a" && a /= "A" = return e
          | findPN name e1 =  return (Exp (HsTuple (makeTuple (pNtoName name) newCount (removeName e) total newAnswer)))
          | findPN name e2 = do newExp <- replaceInE a name total e2
                                return (Exp (HsApp e1 (newExp) ))
          | otherwise = return e'
          
              where
                  (newCount, newAnswer) = countAnswer 0 a
        rename' a e'@(Exp (HsParen e1)::HsExpP) = do newExp <- replaceInE a name total e1
                                                     return (Exp (HsParen (newExp)))
        rename' a e'@(Exp (HsLet ds e1)::HsExpP) = do newDS <- replaceWithNew a name ds total
                                                      newExp <- replaceInE a name total e1
                                                      return (Exp (HsLet newDS newExp))
        rename' a e'@(Exp (HsIf e1 e2 e3)::HsExpP) = do newExp1 <- replaceInE a name total e1
                                                        newExp2 <- replaceInE a name total e2
                                                        newExp3 <- replaceInE a name total e3
                                                        return (Exp (HsIf newExp1 newExp2 newExp3))
                                                      
        rename' a e'@(Exp (HsTuple (e1:e1s))::HsExpP) = do newExp1 <- replaceInE a name total e1
                                                           newExps2 <- mapM (replaceInE a name total) e1s
                                                           return (Exp(HsTuple (newExp1 : newExps2)))
                    
        rename' a e'@(Exp (HsList (e1:e1s))::HsExpP) = do newExp1 <- replaceInE a name total e1
                                                          newExps2 <- mapM (replaceInE a name total) e1s
                                                          return (Exp(HsList (newExp1 : newExps2)))
                                                        
        rename' a e'@(Exp (HsLambda ps e1)::HsExpP) = do newExp1 <- replaceInE a name total e1
                                                         return (Exp (HsLambda ps newExp1))
                            
        rename' a e'@(Exp (HsInfixApp e1 i e2)::HsExpP) = do newExp1 <- replaceInE a name total e1
                                                             newExp2 <- replaceInE a name total e2
                                                             return (Exp(HsInfixApp newExp1 i newExp2))
                                                           
        rename' a e'@(Exp (HsCase e1 as)::HsExpP) = do newExp1 <- replaceInE a name total e1
                                                       newAlts <- mapM (replaceInA name total) as
                                                       return (Exp (HsCase newExp1 newAlts))
                                                        where
                                                         replaceInA name total (HsAlt s p (HsBody e1) ds) 
                                                          = do
                                                               newExp1 <- replaceInE a name total e1
                                                               newDS <- replaceWithNew a name ds total
                                                               return (HsAlt s p (HsBody newExp1) newDS)
                                                             
                                                         replaceInA name total (HsAlt s p (HsGuard es) ds) 
                                                          = do
                                                         
                                                             newExp1 <- mapM replaceInG es
                                                             newDS <- replaceWithNew a name ds total
                                                             return (HsAlt s p (HsGuard newExp1) newDS)
                                                              where
                                                               replaceInG (s, e1, e2) = do newExp1 <- replaceInE a name total e1
                                                                                           newExp2 <- replaceInE a name total e2
                                                                                           return (s, newExp1, newExp2) 
                                                             
                                                      
        rename' a (x::HsExpP) 
            | findPN name x = return (Exp (HsTuple (makeSimpleTuple (pNtoName name) newCount total newAnswer)))
            | otherwise = return x
                where
                  (newCount, newAnswer) = countAnswer 0 a
        
 
makeTuple _ _ _ 0 _= []
makeTuple name i e2 total a
 =  (Exp (HsApp (nameToExp (name ++ (show i))) e2)) : (makeTuple name newCount e2 (total-1) newAnswer) 
    where
       (newCount, newAnswer) = countAnswer 0 a
makeTuple2 _ _ _ 0 _ = []
makeTuple2 name i e1 total a
 =  (Exp (HsApp e1 (nameToExp (name ++ (show i))))) : (makeTuple2 name newCount e1 (total-1) newAnswer) 
    where
       (newCount, newAnswer) = countAnswer 0 a
makeSimpleTuple _ _ 0 _ = []
makeSimpleTuple name i total a
 = (nameToExp (name ++ (show i))) : (makeSimpleTuple name newCount (total-1) newAnswer)  
     where
         (newCount, newAnswer) = countAnswer 0 a  

 
sortDecls :: ([HsDeclP], [Bool], [PNT]) -> [(HsDeclP, Bool, PNT)]
sortDecls ([],_, _) = []
sortDecls ((d@(Dec (HsFunBind loc (m@(HsMatch l i1 ps (HsBody e) ds):ms))):dss), (b:bs), (s:ss))
 = (( (d, b, s) : (findRest i1 (dss, bs, ss) )) ++ sortDecls ((map (\(a,b,c) -> a) (removeAll i1 ((d:dss), (b:bs) , (s:ss))) ) , (map (\(a,b,c) -> b) (removeAll i1 ((d:dss), (b:bs), (s:ss) ))  ), (map (\(a,b,c)->c) (removeAll i1 ((d:dss), (b:bs), (s:ss))))   ) )
   where
      findRest :: PNT -> ([HsDeclP], [Bool], [PNT]) -> [(HsDeclP, Bool, PNT)]
      findRest i ([], _, _) = []
      findRest i ((d@(Dec(HsFunBind loc (m@(HsMatch l i1 ps (HsBody e) ds):ms))):dss), (b:bs), (s:ss))
        | i == i1 = (d, b, s) : (findRest i (dss, bs, ss))
        | otherwise = findRest i (dss, bs, ss)
      findRest i (_, _, k) = error $ show k
    
      removeAll :: PNT -> ([HsDeclP], [Bool], [PNT]) -> [(HsDeclP, Bool, PNT)]
      removeAll i ([], _, _) = []
      removeAll i ((d@(Dec(HsFunBind loc (m@(HsMatch l i1 ps (HsBody e) ds):ms))):dss) , (b:bs), (s:ss) )                    
        | i == i1 = removeAll i (dss, bs, ss)
        | otherwise = (d,b, s) : (removeAll i (dss, bs, ss) )
 
        
correctExpression [] exp  = exp
correctExpression (x:xs) exp
      | x == defaultExp = correctExpression xs exp
      | otherwise = x
 
get1Element :: HsExpP -> HsExpP
get1Element (Exp (HsTuple (e:es))) = e
get1Element e = e 
 
  
forEach [] _ _ _ fileName i a _ (inscps, exps, mod, tokList) 
 = do    
       return []
                              
forEach (e:es) rhs wh wh3 fileName i a (funName, funPats) (inscps, exps, mod, tokList)  
  = do
        let (newCount, newAnswer) = countAnswer i a          

        let (begin, end) = getStartEndLoc tokList (get1Element e)
        let (loc, pnt, pats, exp, wh2, p)
                  = findDefNameAndExp tokList
                                      begin
                                      end
                                      mod 
                                      
                                      
        -- error $ "1" ++ (show (begin, end))
        res <- checkLetAndLambda begin end tokList wh e rhs
        let res' = correctExpression res rhs
        newExp' <- checkIfOrLet res' e tokList begin end
        (refactoredExp,wh') <- checkCase newExp' e wh
        res1 <- sliceSubExp p rhs refactoredExp wh' wh3 (head loc) funName pats newCount         
        res2 <- forEach es rhs wh wh3 fileName newCount newAnswer (funName, funPats) (inscps, exps, mod, tokList)
        return (res1 ++ res2)
        
forEach2 wher [] rhs wh wh3 fileName i a (funName, funPats) (inscps, exps, m, tokList) = do
       return []
                              
forEach2 wher (e:es) rhs wh wh3 fileName i a (funName, funPats) (inscps, exps, m, tokList)
  = do
        let (newCount, newAnswer) = countAnswer i a          



        let (begin, end) = getStartEndLoc tokList (get1Element e)
        let blah@(loc, pnt, pats, exp, wh2, p)
                  = findDefNameAndExp tokList
                                      begin
                                      end
                                      m 
        let (begin2, end2) = getStartEndLoc tokList rhs
        
        -- error $ "2" ++ (show (loc, pnt, pats, exp, wh2, p) )

        let (_,_, mainPats, _, _,_)
                  = findDefNameAndExp tokList
                                      begin2
                                      end2
                                      m   
                                                                               
        res <- checkLetAndLambda begin end tokList wh e rhs
        let res' = correctExpression res rhs
        newExp' <- checkIfOrLet res' e tokList begin end
        (refactoredExp,wh') <- checkCase newExp' e wh
                
        res1 <- sliceSubExp3 wher rhs e pnt p refactoredExp wh' wh3 (head loc) pnt mainPats funPats newCount
        res2 <- forEach2 wher es rhs wh wh3 fileName newCount newAnswer (funName, funPats) (inscps, exps, m, tokList)
        
        -- error $ show (res1 ++ res2)
        
        return (res1 ++ res2)

countAnswer :: Int -> String -> (Int, String)
countAnswer i [] = (i, [])
countAnswer i "a" = (i+ 1, "a")
countAnswer i "A" = (i+ 1, "a")
countAnswer i ('_':xs) = countAnswer (i+1) xs
countAnswer i ('x':xs) = ((i+1), xs)
countAnswer i ('X':xs) = ((i+1), xs)
countAnswer i (x:xs)  =  countAnswer i xs


sliceSubExp2 (_,_,mod) = return mod                                   
sliceSubExp p old exp wh wh2 loc pnt pats i -- (_,_, mod) 
   = do
       (decls, newExp) <- removeRedun wh exp  
       return (updating p loc pnt pats newExp decls i)
                                                 
sliceSubExp3 wher funRHS rhs funName p old wh wh2 loc pnt mainPats pats i -- (_,_, mod) 
   = do
       (decls, newExp) <- removeRedun wh rhs
       newWher <- removeRedunWhere wher rhs
       return [(newDecl3 loc (nameToPNT ((pNTtoName funName) ++ (show i))) pats newExp decls i)]
       
       
       -- return (updating2 p (wh2++newWher) funRHS funName loc pnt mainPats pats newExp decls i)
                                                                                                                                                                            
changeName newName (PNT (PN (UnQual _) (G modName _ optSrc)) Value s) 
                  = PNT (PN (UnQual newName) (G modName newName optSrc)) Value s
                                                             
updating (match@(Match x)) loc pnt pats rhs ds i=  [Dec (HsFunBind loc0 [newMatch loc pnt pats rhs ds i])]
                                                        
updating (pat@(MyPat x))loc pnt pats rhs ds i = [newDecl loc pnt pats rhs ds i]

updating x _ _ _ _ _ _ = error $ show x

updating2 (match@(Match x)) wher funRHS funName loc pnt mainPats pats rhs ds i=  [Dec (HsFunBind loc0 [newMatch2 wher funRHS funName loc pnt mainPats pats rhs ds i])]
                                                      
updating2 (pat@(MyPat x)) wher funRHS funName loc pnt mainPats pats rhs ds i = [newDecl2 wher funRHS funName loc pnt mainPats pats rhs ds i]

newMatch loc pnt pats rhs ds i= HsMatch loc (nameToPNT ((pNTtoName pnt) ++ (show i))) pats (HsBody rhs) ds 
newDecl loc pnt pats rhs ds i = Dec (HsFunBind loc [HsMatch loc (nameToPNT ((pNTtoName pnt) ++ (show i))) pats (HsBody rhs) ds] )

newMatch2 wher funRHS funName loc pnt mainPats pats rhs ds i= HsMatch loc (nameToPNT ((pNTtoName funName) ++ (show i))) mainPats (HsBody funRHS) ([newDecl3 loc pnt pats rhs ds i] ++ wher)

newDecl2 wher funRHS funName loc pnt mainPats pats rhs ds i = Dec (HsFunBind loc [HsMatch loc (nameToPNT ((pNTtoName funName) ++ (show i)))  mainPats (HsBody funRHS) ([newDecl3 loc pnt pats rhs ds i] ++ wher)] )

newDecl3 loc pnt pats rhs ds i = Dec (HsFunBind loc [HsMatch loc pnt pats (HsBody rhs) ds] )


getRHS :: String -> String -> HsDeclP -> PNT -> Bool -> [HsDeclP] -> String -> [([HsExpP], HsExpP, [HsDeclP], [HsDeclP], Bool, [HsPatP])]              
getRHS fileName a (Dec (HsPatBind loc p (HsBody e) ds)) pnt local localDefs modName
 = res e
     where
      res e =
       case e of
        (Exp (HsTuple es)) -> if (getLength1 a e) == (length es)
                                 then [(es, e, ds, [],  local, [p])]
                                 else do let l = getLengthAnswer a 0 
                                         if (length es) /= l
                                            then error "Please supply the correct number of elements"
                                            else [((shuffleRHS a es), e, ds, [], local, [p])]   
        (Exp (HsId (HsVar i)))     
             -> do
                    let types = getTypes fileName (pNTtoName (patToPNT p) ) modName
                    let returnType = last types
                    if local == False
                      then do
                        let isTuple = elem '(' returnType && elem ',' returnType && elem ')' returnType
                        if isTuple 
                         then
                          if or (map (defines (pNTtoPN i)) ds)
                            then 
                              do
                                -- find the definition
                                let def = findDef i ds
                                if def == []
                                  then error "Definition does not appear on the RHS"
                                  else
                                   do
                                    let ((listExp, rhs, wh, wh2, localDefs, p'):xs) = (getRHS fileName a (head def) i True ds modName)
                                    ((listExp, e, wh, wh2, True, p'):xs)

                            else
                               error "Definition does not appear on the RHS"
                         else error $ show isTuple
                      else
                        if or (map (defines (pNTtoPN i)) ds)
                         then 
                           do
                             -- find the definition
                             let def = findDef i ds
                             if def == []
                               then error "Definition not defined on RHS"
                               else
                                 do
                                   let ((listExp, rhs, wh, wh2, localDefs, p'):xs) = (getRHS fileName a (head def) i True ds modName)
                                   ((listExp, e, wh, wh2, True, p'):xs)
                         else
                            error "Definition not definied on RHS"
        (Exp (HsApp e1 e2)) -> do let ((listExp, e', wh, wh2, True, p'):xs) =  res e1
                                  ((listExp, e, wh, wh2, True, p'):xs)
        _  -> [([e], e, ds,[], False, [p])]   

     
getRHS fileName a (Dec (HsFunBind loc ms)) pnt local localDefs modName
 = findInMatch ms pnt
     where
       findInMatch [] _ = []
       findInMatch (m@(HsMatch l i1 ps (HsGuard [(s, e1, e2)]) ds):ms) pnt
          = findInMatch ((HsMatch l i1 ps (HsBody e2) ds):ms) pnt
       findInMatch (m@(HsMatch l i1 ps (HsBody e) ds):ms) pnt
          = (res e) ++ (findInMatch ms pnt)
             where  
               mapM2 f [e] = do let ((listExp, e', wh, wh2, localDefs, p):xs) = res e
                                ((listExp, e, wh, wh2, True, p):xs)
               mapM2 f (e:es) = do let ((listExp, e', wh, wh2, localDefs, p):xs) = res e
                                   (((e:es), e, wh, wh2, True, p):xs) ++ mapM2 f es
               res e = 
                 case e of
                   (Exp (HsTuple es)) -> if (getLength1 a e) == (length es)
                                           then [(es, e, ds, [],  local, ps)]
                                           else do let l = getLengthAnswer a 0 
                                                   if (length es) /= l
                                                    then error "Please supply the correct number of elements"
                                                    else [((shuffleRHS a es), e, ds, [], local, ps)] -- [((shuffleRHS a es), e, ds, [], False)]                   
                   (Exp (HsId (HsVar i)))   
                      -> do
                          let types = getTypes fileName (pNTtoName i1) modName
                          let returnType = last types
                          if local == False
                            then do
                                   let isTuple = elem '(' returnType && elem ',' returnType && elem ')' returnType                              
                                   if isTuple 
                                         then
                                              if or (map (defines (pNTtoPN i)) ds)
                                                then 
                                                  do
                                                   -- find the definition
                                                   let def = findDef i ds
                                                   if def == []
                                                     then error ("Definition does not appear on the RHS" ++ (show i))
                                                     else
                                                       do
                                                        let ((listExp, rhs, wh, wh2, localDefs, p):xs) = (getRHS fileName a (head def) i True ds modName)
                                                        ((listExp, e, wh, wh2, True, p):xs)
                                                else
                                                   error "Definition does not appear on the RHS"
                                         else error $ show isTuple
                                    else
                                     if or (map (defines (pNTtoPN i)) ds)
                                                then 
                                                  do
                                                   -- find the definition
                                                   let def = findDef i ds
                                                   if def == []
                                                     then error $ show def
                                                     else
                                                       do
                                                        [([e], e, ds, [] ,True, ps)]

                                                else do
                                                   -- let def = definingDecls [(nameToPN (pNTtoName i))] localDefs False False
                                                   let def = findDef i localDefs
                                                   if def == []
                                                    then error ( "Definition does not fully appear on RHS" ++ (show i) )
                                                    else
                                                     do
                                                      let newDec = (Dec (HsFunBind loc [m]))
                                                      [([e], e, ds, [] ,True, ps)]
                   (Exp (HsApp e1 e2)) -> do let ((listExp, e', wh, wh2, True, p):xs) =  res e1
                                             ((listExp, e, wh, wh2, True, p):xs)
                   e -> [([e], e, ds,[], False, ps)]        
       -- findInMatch m pnt = error $ show m           
findDef pnt t
 = fromMaybe ([])
    (applyTU (once_tdTU (failTU `adhocTU` inDef)) t)                                       
     where
      inDef d@(Dec (HsPatBind loc p (HsBody e) ds)) 
        | pNTtoName (patToPNT p) == pNTtoName pnt = Just [d]
        | otherwise                    = Nothing
      inDef d@(Dec (HsFunBind loc ms))
        | traverseMS ms = Just [d]
        | otherwise     = Nothing
            where
              traverseMS [] = False
              traverseMS (m@(HsMatch l i1 ps (HsBody e) ds):ms)
               | pNTtoName i1 == pNTtoName pnt = True
               | lookInPats ps pnt = True
               | otherwise = traverseMS ms
      inDef _ = Nothing
      
lookInPats [] _ = False      
lookInPats (p:ps) pnt 
  | patToPNT p == pnt = True
  | otherwise         = lookInPats ps pnt
      
simpleGetRHS (Dec (HsPatBind loc p (HsBody e) ds)) pnt  = (e, patToPNT p, ds, [])
simpleGetRHS (Dec (HsFunBind loc ms)) pnt 
   = findInMatch ms pnt
       where
        findInMatch [] _ = (defaultExp, defaultPNT, [], [])
        findInMatch (m@(HsMatch l i ps (HsBody e) ds):ms) pnt
         | findPNT pnt m = (e, i, ds, ps) 
         | otherwise     = findInMatch ms pnt
        findInMatch (m@(HsMatch l i ps (HsGuard [(l', e1, e2)]) ds):ms) pnt
         | findPNT pnt m = (e2, i, ds, ps)
         | otherwise     = findInMatch ms pnt 
         
removeFromWhere [] _ = []         
removeFromWhere (d:ds) pnt 
 | defines pnt d = removeFromWhere ds pnt
 | otherwise     = d : (removeFromWhere ds pnt)
                                 

--check whether the cursor points to the beginning of the datatype declaration
--taken from RefacADT.hs
checkCursor :: String -> Int -> Int -> HsModuleP -> Either String HsDeclP
checkCursor fileName row col mod
 = case locToTypeDecl of
     Nothing -> Left ("Invalid cursor position. Please place cursor at the beginning of the definiton!")
     Just decl -> Right decl
   where
    locToTypeDecl = find (definesPNT (locToPNT fileName (row, col) mod)) (hsModDecls mod)
    
    definesPNT pnt d@(Dec (HsPatBind loc p e ds))
      = findPNT pnt d
    definesPNT pnt d@(Dec (HsFunBind loc ms)) = findPNT pnt d
    definesPNT pnt _ = False
    
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
      inMatch (match@(HsMatch loc1 pnt pats (rhs@(HsGuard [(s, e1, e2)])) ds)::HsMatchP)
        | locToExp beginPos endPos toks rhs /= defaultExp
          = Just ([loc1], pnt, pats, e2, ds, (Match match))
      inMatch _ = Nothing

      --The selected sub-expression is in the rhs of a pattern-binding
      inPat (pat@(Dec (HsPatBind loc1 ps (rhs@(HsBody e)) ds))::HsDeclP)
        | locToExp beginPos endPos toks rhs /= defaultExp
          = if isSimplePatBind pat
              then Just ([loc1], patToPNT ps, [], e, ds, (MyPat pat))
              else error "A complex pattern binding can not be generalised!"
      inPat _ = Nothing
      
    
    
