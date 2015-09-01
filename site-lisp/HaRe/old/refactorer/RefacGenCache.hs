module RefacGenCache where

import TypeCheck
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
import PFE0 (findFile, allFiles, allModules)
import MUtils (( # ))
import RefacLocUtils
-- import System
import System.IO
import Relations
import Ents
import Data.Set (toList)
import Data.List
import System.IO.Unsafe
import System.Cmd
import LocalSettings (genFoldPath)

-- allows the selection of a function equation to
-- be outputted as AST representation to a file.

genFoldCache args
 = do
     let fileName     = args!!0
         begin        = read (args!!1)::Int
         end          = read (args!!2)::Int

     (inscps, exps, mod, tokList) <- parseSourceFile fileName

     case checkCursor fileName begin end mod of
         Left errMsg -> do error errMsg
         Right decl ->
           do
              AbstractIO.writeFile genFoldPath (show decl)
              AbstractIO.putStrLn "refacGenFoldCache"

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
