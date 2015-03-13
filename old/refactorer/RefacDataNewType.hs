module RefacDataNewType (refacDataNewType) where
 

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

refacDataNewType args
  = do let fileName   = args!!0
           row   = read (args!!1)::Int
           col   = read (args!!2)::Int
       -- Parse the input file.
       modInfo@(inscps, exps, mod, tokList) <- parseSourceFile fileName

       -- Find the function that's been highlighted as the refactree

       --let pat = locToPNT fileName (row,col) mod

     {-  let dat
             = findDefNameAndExp tokList
                                 (beginRow, beginCol)
                                 (endRow, endCol)
                                 mod -}

       AbstractIO.putStrLn "Warning: This refactoring may change the strictness properties of the program."
       case checkCursor fileName row col mod of
         Left errMsg -> do error errMsg
         Right dat ->
           do

     --  error (show pat)

             refactoredMod <- applyRefac (addNewType dat) (Just modInfo) fileName
   --    refactoredMod <- forEach exp (beginRow, beginCol) (endRow, endCol) tokList wh p loc pnt pats 1 modInfo fileName ((fileName, False), (tokList, mod))
             writeRefactoredFiles False [refactoredMod]

             AbstractIO.putStrLn "Completed.\n"

addNewType dataDec (_,_, mod) = do
                     let newType = createNewType dataDec
               -- res <- addDecl mod Nothing ([newType], Nothing) True
                     res <- update dataDec newType mod
                     return res

createNewType (dec@(Dec (HsDataDecl loc n tp (c:cs) is)))
  = if checkLength c == False then error "constructor must have exactly one argument."
                    else Dec (HsNewTypeDecl loc n tp c is)

createNewType _ = error "not a valid data expression"

checkLength (HsConDecl src is c i ds)
 = if length ds > 1 then False
                    else True
checkLength _ = True

{-|
Takes the position of the highlighted code and returns
the function name, the list of arguments, the expression that has been
highlighted by the user, and any where\/let clauses associated with the
function. 
-}

findDefNameAndExp :: Term t => [PosToken] -- ^ The token stream for the 
                                          -- file to be
                                          -- refactored.
                  -> (Int, Int)
                  -> (Int, Int)
                  -> t          -- ^ The abstract syntax tree.
                  -> [HsDeclP] -- ^ A tuple of,
                     -- (the function name, the list of arguments,
                     -- the expression highlighted, any where\/let clauses
                     -- associated with the function).
                    
findDefNameAndExp toks beginPos endPos t
  = fromMaybe []
              (applyTU (once_tdTU (failTU `adhocTU` inDat)) t)

    where
      {---The selected sub-expression is in the rhs of a match
      inMatch (match@(HsMatch loc1  pnt pats (rhs@(HsBody e)) ds)::HsMatchP)
        | locToExp beginPos endPos toks rhs /= defaultExp
          = Just ([loc1], pnt, pats, e, ds)
      inMatch _ = Nothing

      --The selected sub-expression is in the rhs of a pattern-binding
      inPat (pat@(Dec (HsPatBind loc1 ps (rhs@(HsBody e)) ds))::HsDeclP)
        | locToExp beginPos endPos toks rhs /= defaultExp
          = if isSimplePatBind pat
              then Just ([loc1], patToPNT ps, [], e, ds)
              else error "A complex pattern binding can not be generalised!"
      inPat _ = Nothing-}

      inDat (dat@(Dec(HsDataDecl loc n tp cs is))::HsDeclP)
        | locToExp beginPos endPos toks dat /= defaultExp
        = if length cs > 1 
            then error "You can only create a newtype from a data type with one constuctor"
            else Just [dat]
      inDat _ = Nothing

--check whether the cursor points to the beginning of the datatype declaration
--taken from RefacADT.hs
-- checkCursor :: String -> Int -> Int -> HsModuleP -> Either String HsDeclP
-- checkCursor fileName row col mod
--  = case locToTypeDecl of
--      Nothing -> Left ("Invalid cursor position. Please place cursor at the beginning of the type constructor name!")
--      Just decl -> Right decl
--    where
--     locToTypeDecl = find (definesTypeCon (locToPNT fileName (row, col) mod)) (hsModDecls mod)
    
--     definesTypeCon pnt (Dec (HsDataDecl loc c tp xs _)) 
--       = if length xs > 1 then error "You must select a data type with only one constructor"
--                          else isTypeCon pnt && (findPNT pnt tp)
--     definesTypeCon pnt _ = False


checkCursor :: String -> Int -> Int -> HsModuleP -> Either String HsDeclP
checkCursor fileName row col mod
 = case locToTypeDecl of
     Nothing -> Left ("Invalid cursor position. Please place cursor at the beginning of the type constructor name!")
     Just decl@(Dec (HsDataDecl loc c tp xs _)) ->
         if length xs >1 then Left (error " You must select a data type with only one constructor!")
            else Right decl          
   where
    locToTypeDecl = find (definesTypeCon (locToPNT fileName (row, col) mod)) (hsModDecls mod)
    
    definesTypeCon pnt (Dec (HsDataDecl loc c tp xs _)) 
      = isTypeCon pnt && (findPNT pnt tp)
    definesTypeCon pnt _ = False
