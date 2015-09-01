module RefacDuplicates(detectDuplicates,detectSpecDuplicates) where

import PrettyPrint
import PosSyntax
import Data.Maybe
import TypedIds

import UniqueNames hiding (srcLoc)
import PNT
import TiPNT

import Data.List as List
import RefacUtils
import PFE0 (findFile, getCurrentModuleGraph)
import AbstractIO
import Prelude hiding (putStrLn, putStr)
import Data.Char
import System.Time

type Drip = (String, LocInfo)
type ExpDrip = (HsExpP, LocInfo)
type Bucket = [Drip]
type ExpBucket = [ExpDrip]
type BucketGroup = [Bucket]
type ExpBucketGroup = [ExpBucket]
type LocInfo = (String, Int, Int)


-- **************************************************
-- *****                                        *****
-- ***** File:        RefacDuplicates.hs        *****
-- ***** Module Name: RefacDuplicates           *****
-- ***** Author:      Jonathan Cowie            *****
-- ***** Email:       jrc3@kent.ac.uk           *****
-- *****                                        *****
-- ***** Created as a summer internship project *****
-- ***** between July and August 2004           *****
-- *****                                        *****
-- **************************************************

detectDuplicates args
 = do let fileName  = args!!0
      timeone <- AbstractIO.getClockTime
      modName <- fileNameToModName fileName

      (inscps, exps, mod, tokList) <- parseSourceFile fileName
      putStrLn "\nComputing list of duplicates from the following files..."
      servers<-serverModsAndFiles modName
      let directory = getDirectory fileName
          servers' = stripServers servers directory
      -- mods <- getModules
      putStrLn $ show servers'
      expmods <- makeFullASTList (map snd servers')
      let dups = getDuplicates expmods
      displayDuplicates dups
      putStrLn "Duplicate code refactoring complete!\n"
      timetwo <- AbstractIO.getClockTime
      putStrLn $ show $ diffClockTimes timetwo timeone

getDirectory :: String -> String
getDirectory f
  = reverse $ dropWhile (=='/') (dropWhile (/='/') (reverse f))

-- stripServers :: [(ModuleName, String)] -> String -> [(ModuleName, String)]
stripServers [] d = []
stripServers (a@(x,y):xs)  d
 | d == getDirectory y = a : stripServers xs d
 | otherwise           = stripServers xs d

detectSpecDuplicates args
 = do let fileName   = args!!0
          beginRow   = read (args!!1)::Int
          beginCol   = read (args!!2)::Int
          endRow     = read (args!!3)::Int
          endCol     = read (args!!4)::Int
      timeone <- AbstractIO.getClockTime
      modName <- fileNameToModName fileName
      (inscps, exps, mod, tokList) <- parseSourceFile fileName
      let exp=findExp tokList (beginRow, beginCol) (endRow, endCol) mod
      if exp/=defaultExp
        then  -- (mod',((tokList',_),_))<- detectDuplicates' fileName (beginRow,beginCol)(endRow,endCol) mod tokList
              -- writeRefactoredFiles [((fileName,True), (tokList',mod'))]
              do putStrLn "\nComputing list of duplicates from the following files..."
		 mods <- getModules
	 	 putStrLn $ show mods
		 expmods <- makeFullASTList mods
                 let dups = getSpecificDupls exp expmods
                 displayDuplicates dups
                 putStrLn "Duplicate code refactoring complete!\n"
        else  putStrLn "You have not selected a valid expression!\n"
      timetwo <- AbstractIO.getClockTime
      putStrLn $ show $ diffClockTimes timetwo timeone
  where


  findExp toks beginPos endPos t
     =fromMaybe defaultExp (applyTU (once_tdTU (failTU `adhocTU` exp)) t)
       where exp (e::HsExpP)
               |inScope (getStartEndLoc toks e)=Just e
             exp _ =Nothing

             inScope (startLoc,endLoc)
                =startLoc>=beginPos &&  endLoc<=endPos



-- ***********************************************************
-- ***** HashTable construction & manipulation functions *****
-- ***********************************************************

--Takes an AST and returns a bucket containing (for each drip) the string of the Expression
--name, and the start & finish locations of the Expression
makeBucket :: Term t => t -> Bucket
makeBucket ast = ghead "makeBucket"  $ applyTU (stop_tdTU (failTU `adhocTU` addHash)) ast
    where addHash (a::HsExpP)= return [(showExp a,getSrcLoc a)]

--Simple hash function, Takes a String and returns an Int
--Currently not used, but left in just in case
hashString :: String -> Int
hashString = fromIntegral . foldr f 0
    where f c m = ord c + (m * 128) `rem` 1500007

--Takes an AST of Type Exp and returns its start location
getSrcLoc :: (Term t) => t -> LocInfo
getSrcLoc exp  = if length lexp == 0 then ("",0,0) else ghead "getSrcLoc" lexp
    where lexp = allSortedLocsRev exp

--Takes an AST and returns the AST with all SrcLocs replaced with loc0
removeSrcLocs :: Term t => t -> t
removeSrcLocs ast =  ghead "removeSrcLocs" $ applyTP (full_tdTP (idTP `adhocTP` noSrc)) ast
    where noSrc (a::SrcLoc) = return loc0

--Takes a single Drip parameter, a Bucket and returns the Bucket with
--all occurences of the Drip parameter removed
removeHashElement :: Drip -> Bucket ->  Bucket
removeHashElement (x,y) xs = [(a,b) | (a,b) <- xs, a /= x]

--Takes an expression and returns a string containing the data constructor name
showExp :: HsExpP -> String
showExp exp = case exp of
              (Exp (HsId (HsVar _))) -> "HsVar"
	      (Exp (HsId (HsCon _))) -> "HsCon"
              (Exp (HsLit _ _)) -> "HsLit"
              (Exp (HsInfixApp _ _ _)) -> "HsInfixApp"
              (Exp (HsApp _ _)) -> "HsApp"
              (Exp (HsNegApp _ _)) -> "HsNegApp"
              (Exp (HsLambda _ _)) -> "HsLambda"
              (Exp (HsLet _ _)) -> "HsLet"
              (Exp (HsIf _ _ _)) -> "HsIf"
              (Exp (HsCase _ _)) -> "HsCase"
              (Exp (HsDo _)) -> "HsDo"
              (Exp (HsTuple _)) -> "HsTuple"
              (Exp (HsList _)) -> "HsList"
              (Exp (HsParen _)) -> "HsParen"
              (Exp (HsLeftSection _ _)) -> "HsLeftSection"
              (Exp (HsRightSection _ _)) -> "HsRightSection"
              (Exp (HsRecConstr _ _ _)) -> "HsRecConstr"
              (Exp (HsRecUpdate _ _ _)) -> "HsRecUpdate"
              (Exp (HsEnumFrom _)) -> "HsEnumFrom"
              (Exp (HsEnumFromTo _ _)) -> "HsEnumFromTo"
              (Exp (HsEnumFromThen _ _)) -> "HsEnumFromThen"
              (Exp (HsEnumFromThenTo _ _ _)) -> "HsEnumFromThenTo"
              (Exp (HsListComp _)) -> "HsListComp"
              (Exp (HsExpTypeSig _ _ _ _)) -> "HsExpTypeSig"
              (Exp (HsAsPat _ _)) -> "HsAsPat"
              (Exp (HsWildCard)) -> "HsWildCard"
              (Exp (HsIrrPat _)) -> "HsIrrPat"


--Takes an AST and returns a list of tuples containing the string equivalent of the
-- Expression name, and the start & finish locations of the Expression
genExpList :: (Term t) => t -> [HsExpP]
genExpList ast = ghead "genExpList" $ applyTU (stop_tdTU ( failTU `adhocTU` isExp)) ast
    where isExp (a::HsExpP)= return [a]

--Modified version of allSortedLocs to include Filename
allSortedLocsRev t =(sort.nub.getSrcLocsRev) t

--Modified version of getSrcLocs to include Filename
getSrcLocsRev=runIdentity.(applyTU (full_tdTU (constTU [] `adhocTU` pnt
                                                       `adhocTU` literalInExp
                                                       `adhocTU` literalInPat)))
        where
            pnt (PNT pname _ (N (Just (SrcLoc f c row col))))=return [(f,row,col)]
            pnt _=return []

            literalInExp ((Exp (HsLit (SrcLoc f  c row col) _))::HsExpP) = return [(f,row,col)]
            literalInExp (Exp _) =return []

            literalInPat ((Pat (HsPLit (SrcLoc f c row col) _))::HsPatP) = return [(f,row,col)]
            literalInPat (Pat (HsPNeg (SrcLoc f c row col) _)) = return [(f,row,col)]
            literalInPat _ =return []




-- **********************************************************
-- ***** Initial duplicate list  construction functions *****
-- **********************************************************

--Takes a Bucket, a DuplicateData List and populates the list with all duplicates
--found in the Bucket
constructBucketGroup :: Bucket -> BucketGroup -> BucketGroup
constructBucketGroup hshtbl dupl
		= case hshtbl of
                      []  -> dupl
                      (x:xs) -> if (dripOccurences x xs) > 1
			        then (addAllOcc x xs dupl) ++ (constructBucketGroup (removeHashElement x xs) [])
			        else dupl ++ (constructBucketGroup xs [])

--Takes a single Drip parameter, a Bucket and returns the number of times
--the Drip parameter occurs in the Bucket
dripOccurences :: Drip -> Bucket -> Int
dripOccurences (x,y) xs = 1 + length [a | (a,b) <- xs, a == x]

--Takes a single Drip parameter, a Bucket and a BucketGroup and populates it
--with all occurences of Drip in Bucket
addAllOcc :: Drip -> Bucket -> BucketGroup -> BucketGroup
addAllOcc (x,y) xs dupl = ((x,y) : [(a,b) | (a,b) <- xs, a == x])  : dupl



-- *********************************************************
-- ***** Initial duplicate list verification functions *****
-- *********************************************************

--Takes a BucketGroup parameter and populates it with full expressions from the
--HsExpP list taken as the first parameter
--Returns ExpBucketGroup
populateBucketGroup :: [HsExpP] -> BucketGroup -> ExpBucketGroup
populateBucketGroup expl [] = []
populateBucketGroup expl (x:xs) = map (getExp expl) x : populateBucketGroup expl xs
    where getExp ast dupl = ghead "populateBucketGroup" (catMaybes $ map (getMatch dupl) ast)
          getMatch (strexp, locinfo) exp
            | (getSrcLoc exp) == locinfo && strexp == showExp exp  = Just ((removeSrcLocs exp), locinfo)
            | otherwise                  = Nothing

--Takes an ExpBucket (second param is list to store intermediate results)
--and groups the elements according to duplicate matches
--Returns ExpBucket
groupDupls ::  ExpBucket -> ExpBucket -> ExpBucket
groupDupls  y []= y
groupDupls  ys (x:xs) = let r = xmatches x xs
		        in groupDupls (ys++r) (xs\\r)
    where xmatches x xs = x:filter (\y->(show (fst x)) == (show (fst y))) xs

--Given an ExpBucketGroup paramater, returns a grouped list of
--duplicate Expressions in ExpBucketGroup form.
elemCheck :: ExpBucketGroup -> ExpBucketGroup
elemCheck xs = List.groupBy (\x y ->(show(fst x)) == (show(fst y))) (groupDupls [] (concat xs))

--Takes a list of HsExpP and a BucketGroup list and verifies the duplicates in the BucketGroup list
--against the HsExpP list
verifyBucketGroup :: [HsExpP] -> BucketGroup -> ExpBucketGroup
verifyBucketGroup ast dupl = do let expast = populateBucketGroup ast dupl
			        [ x | x <- elemCheck expast, length x > 1]



-- *******************************************************
-- ***** Module list related functions called by the *****
-- ***** refactor interface                          *****
-- *******************************************************

--Takes a single parameter containing a list of all the modules to be
--expanded into ASTs
makeFullASTList gf= do gh <- (mapM parseSourceFile gf)
		       return [mod | (inscps, exps, mod, tokList) <- gh]

--Returns a list of all modules used in the program which are in the
--same directory as the initial file to be refactored
getModules = do gf <- getCurrentModuleGraph
                return  (filterNames [ f | (f, (m,_)) <- gf])

--Takes a single parameter containing a list of strings and returns
--the list with all strings containing the '/' character removed
filterNames :: [String] -> [String]
filterNames xs = [ x | x <- xs, containsSlash x == False]

--Takes a single string paramater and returns a boolean value
--depending on whether or not the string contains the '/' character
containsSlash :: String -> Bool
containsSlash x = if gx x == 0 then False else True
    where gx xs = length [ x | x <- xs, x == '/']



-- **************************************************************
-- ***** Top level functions called by refactorer interface *****
-- **************************************************************

--Takes an AST and returns a list of duplicate information (Type ExpBucketGroup)
getDuplicates :: Term t => t -> ExpBucketGroup
getDuplicates ast = verifyBucketGroup (genExpList ast) (constructBucketGroup (makeBucket ast) [])

--Takes an AST and returns a bucket containing (for each drip) the string of the Expression
--name, and the start & finish locations of the Expression
getSpecificDupls :: Term t => HsExpP -> t -> ExpBucketGroup
getSpecificDupls exp ast =  [catMaybes $ ghead "getSpecificDupls" $ (applyTU (full_tdTU (constTU [] `adhocTU` findMatches)) ast)]
    where findMatches (a::HsExpP)= if show(removeSrcLocs exp) == show(removeSrcLocs a)
				   then return [Just (a,getSrcLoc a)]
				   else return [Nothing]


--Function to display duplicates returned by getDuplicates in a readable format
displayDuplicates dupls = do putStrLn $ "The following duplicates have been identified (File,Line,Char):" ++ "\n"
		             mapM putStrLn (map displayElement dupls)
    where displayElement xs = if length xs == 1
			      then "No duplicates found.\n"
			      else (render.ppi) (fst(ghead "displayElement" xs)) ++ " at location(s) " ++ show (nub [snd x | x <- xs]) ++ "\n"

--Simple function to display the raw data output by getDuplicates
displayDuplicates1 dupls =  putStrLn $ show dupls
