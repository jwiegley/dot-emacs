-----------------------------------------------------------------------------
-- |
-- Module      :  RefacCacheMerge
-- Copyright   :  (c) Christopher Brown 2006
--
-- Maintainer  :  cmb21@kent.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- This module caches definitions into a file to be used
-- with RefacMerge


module RefacCacheMerge where


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

import LocalSettings (mergeFilePath)

refacCacheMerge args
  = do


       let fileName     = args!!0
           begin        = read (args!!1)::Int
           end          = read (args!!2)::Int
       AbstractIO.putStrLn "refacCacheMerge"


       (inscps, exps, mod, tokList) <- parseSourceFile fileName

       case checkCursor fileName begin end mod of
         Left errMsg -> do error errMsg
         Right decl ->
           do
             AbstractIO.putStrLn ((declToName decl) ++ " added to cache.")

             -- let x = unsafePerformIO (do
             AbstractIO.appendFile mergeFilePath (">" ++ fileName ++ "<" ++ "%" ++ (show begin) ++ "%" ++ "&" ++ (show end) ++ "&")
             AbstractIO.putStrLn "Completed" -- )

             AbstractIO.putStrLn "RefacCacheMerge Completed."

-- check whether the cursor points to the beginning of the datatype declaration
-- taken from RefacADT.hs
{- checkCursor :: String -> Int -> Int -> HsModuleP -> Either String HsDeclP
checkCursor fileName row col mod
 = case locToTypeDecl of
     Nothing -> Left ("Invalid cursor position. Please place cursor at the beginning of the definition!")
     Just decl -> Right decl
   where
    locToTypeDecl = find (definesPNT (locToPNT fileName (row, col) mod)) (hsModDecls mod)

    definesPNT pnt d@(Dec (HsPatBind loc p e ds))
      | declToPName2 d == pNTtoPN pnt = True
      | otherwise = definesPNT pnt (hsDecls ds) -- findPNT pnt d
    definesPNT pnt d@(Dec (HsFunBind loc ms))
      | declToPName2 d == pNTtoPN pnt = True
      | otherwise = definesPNT pnt (hsDecls ms)

    -- = -- findPNT pnt d
    definesPNT pnt _ = False -}

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
     {-  locToPName = locToPN fileName (row, col) mod

        definesPNT pnt d@(Dec (HsFunBind loc ms))
         | isDeclaredIn -}
