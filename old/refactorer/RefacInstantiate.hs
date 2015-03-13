-----------------------------------------------------------------------------
-- |
-- Module      :  RefacInstantiate
-- Copyright   :  (c) Christopher Brown 2007
--
-- Maintainer  :  cmb21@kent.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- This module contains a transformation for HaRe.
-- Instantiating Patterns


module RefacInstantiate where


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
-- import LocalSettings

refacInstantiate args
  = do
       let fileName     = args!!0
           begin        = read (args!!1)::Int
           end          = read (args!!2)::Int
           instantPatt  = drop 3 args
       AbstractIO.putStrLn "refacInstantiate"
       (inscps, exps, mod, tokList) <- parseSourceFile fileName
       case findMatch fileName begin end mod of
         Nothing -> do error "You can only instantiate patterns on the LHS of a match!"
         Just (decl, pats) ->
           do
              let pairedPats = pairPatWithInstance pats instantPatt
              res <- findAndReplaceAllPat decl pairedPats
              case checkCursor fileName begin end mod of
               Left errMsg -> do error errMsg
               Right fun ->
                 do
                  let newFun = addMatch fun res
                  ((_,m), (newToks, newMod)) <- applyRefac (addNewPat fun newFun) (Just (inscps, exps, mod, tokList)) fileName
                  writeRefactoredFiles False [((fileName, m), (newToks, newMod))]
                  AbstractIO.putStrLn "Completed.\n"

addMatch :: HsDeclP -> HsMatchP -> HsDeclP
addMatch (Dec (HsFunBind x ms) ) m = (Dec (HsFunBind x (m : ms)))
addMatch x _ = error "You can only instantiate patterns on the LHS of a match!"

addNewPat fun newFun (_, _, mod)
 = do
     newMod <- update fun newFun mod
     return newMod

pairPatWithInstance :: [HsPatP] -> [ String ] -> [ (HsPatP, String) ]
pairPatWithInstance [] _ = []
pairPatWithInstance _ [] = []
pairPatWithInstance ((Pat (HsPLit _ x)):_) (s:ss)
  | convert x /= s && s /= "_" = error "Can only instantiate an identifier!"
pairPatWithInstance (p:ps) (s:ss) = (p, s) : pairPatWithInstance ps ss

convert ::HsLiteral -> String
convert (HsInt x) = show x
convert (HsChar x) = show x
convert (HsString x) = x
convert (HsFrac x) = show x
convert (HsCharPrim x) = show x
convert (HsStringPrim x) = show x
convert (HsIntPrim x) = show x
convert (HsFloatPrim x) = show x
convert (HsDoublePrim x) = show x
convertt (HsLitLit x ) = x

findAndReplaceAllPat :: (Term t, Monad m) => t -> [ (HsPatP, String) ] -> m t
findAndReplaceAllPat t [] = return t
findAndReplaceAllPat t (x:xs)
 = do
      res <- findAndReplacePat t x
      rest <- findAndReplaceAllPat res xs
      return rest

findAndReplacePat :: (Term t, Monad m) => t -> (HsPatP, String) -> m t
findAndReplacePat t (p,s)
  = applyTP (full_tdTP (idTP `adhocTP` inRhs)) t
  where
   inRhs (pnt::PNT)
    | (patToPNT p) == pnt
       = do return (nameToPNT s)
   inRhs x = return x
findMatch :: Term t => String -> Int -> Int -> t -> Maybe (HsMatchP, [HsPatP])
findMatch fileName row col mod
  = applyTU (once_tdTU (failTU `adhocTU` inMatch)) mod
    where
      --The selected sub-expression is in the rhs of a match
      inMatch (match@(HsMatch loc1  pnt pats (rhs@(HsBody e)) ds)::HsMatchP)
        | useLoc (locToPNT fileName (row, col) mod) == useLoc pnt
          = Just (match, pats)
      inMatch _ = Nothing

checkCursor :: String -> Int -> Int -> HsModuleP -> Either String HsDeclP
checkCursor fileName row col mod
 = case locToPName of
     Nothing -> Left ("Invalid cursor position. Please place cursor at the beginning of the definition!")
     Just decl -> Right decl
    where
        locToPName
         = case res of
             Nothing -> find (definesPNT (locToPNT fileName (row, col) mod)) (hsDecls mod)
             _ -> res
        res =  find (defines (locToPN fileName (row, col) mod)) (concat (map hsDecls (hsModDecls mod)))

        definesPNT pnt d@(Dec (HsPatBind loc p e ds))
         = findPNT pnt d
        definesPNT pnt d@(Dec (HsFunBind loc ms))
         = findPNT pnt d
        definesPNT _ _ = False
