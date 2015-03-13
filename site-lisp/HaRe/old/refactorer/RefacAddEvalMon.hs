module RefacAddEvalMon (refacAddEvalMon) where

import PrettyPrint
import PosSyntax
import Data.Maybe
import TypedIds
import UniqueNames hiding (srcLoc)
import PNT 
import TiPNT 
import Data.List  
import RefacUtils
import PFE0 (findFile)
import MUtils(( # ))
import AbstractIO
import Debug.Trace
import RefacMvDefBtwMod (addImport)
import LocalSettings

refacAddEvalMon args
 = do
      let fileName     = args!!0
           beginRow     = read (args!!1)::Int
           beginCol     = read (args!!2)::Int  
           endRow       = read (args!!3)::Int
           endCol       = read (args!!4)::Int
       AbstractIO.putStrLn "refacAddEvalMonCache"

       (inscps, exps, mod, tokList) <- parseSourceFile fileName

       let pnt       = locToPNT fileName (beginRow, beginCol) mod 
       unless (not (isFunPNT pnt mod)) $ error "Cannot spark a function! Please select a pattern binding instead."

       AbstractIO.putStrLn "refacAddEvalMon completed."