module InitGHC(initGHC) where

import Prelude hiding (putStrLn)
import System.IO.Unsafe
import AbstractIO (putStrLn)
import Data.Maybe
import Data.List  
import TypeCheck
import RefacUtils 

initGHC filenames
 = do 
      AbstractIO.putStrLn $ ghcInit filenames
      