

module RefacWhereLet(refacWhereLet) where

import PrettyPrint
import PosSyntax
import AbstractIO
import Maybe
import TypedIds
import UniqueNames hiding (srcLoc)
import PNT
import TiPNT
import List
import RefacUtils hiding (getParams)
import PFE0 (findFile)
import MUtils (( # ))
import RefacLocUtils
import System
import IO

{- This refactoring converts a where into a let. Could potentially narrow the scrope of those involved bindings.
   
   Copyright   :  (c) Christopher Brown 2008

   Maintainer  :  cmb21@kent.ac.uk
   Stability   :  provisional
   Portability :  portable   
   
-}

refacWhereLet args
 = do let fileName = ghead "filename" args 
          --fileName'= moduleName fileName
          --modName  = Module fileName'  
          row      = read (args!!1)::Int
          col      = read (args!!2)::Int
      modName <-fileNameToModName fileName
      (inscps, exps, mod, tokList)<-parseSourceFile fileName 
      AbstractIO.putStrLn "Completed.\n"