{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances, UndecidableInstances, FunctionalDependencies, NoMonomorphismRestriction #-}
module FileUtils where
import Prelude hiding (readFile,writeFile,
		       putStr,putStrLn,getLine,readLn,print,
		       catch,ioError)
import qualified Prelude
import Control.Monad(unless)
import MUtils(( # ),done,read'',readAtEnd)
import AbstractIO

-- Write to the file only if the new contents is different from the old:
updateFile path contents =
  do unchanged <- ((contents==)#readFileNow path) `catch` const (return False)
     unless unchanged $
          do -- GHC lingering file lock workaround:
             removeFile path `catch` const done -- grr!
             writeFile path contents
     return unchanged

-- Write to the file, even if the new contents is the same:
updateFile' path contents =
  do unchanged <- ((contents==)#readFileNow path) `catch` const (return False)
     -- GHC lingering file lock workaround:
     removeFile path `catch` const done -- grr!
     writeFile path contents
     return unchanged

readFileMaybe path = maybeM (read'' "FileUtils.readFileMaybe" # readFile path)
   -- lazy error checking for efficiency

-- Read a whole file immediately to avoid lingering open file handles
readFileNow path =
    do s <- readFile path
       seq (readall s) (return s)
 where
    readall s | length s>=0 = s

readM s = readM' "FileUtils.readM" s

readM' msg s =
  case reads s of
    [(x,r)] | readAtEnd r -> return x
    []                    -> fail $ msg++": no parse"
    _                     -> fail $ msg++": ambiguous parse"

--readLn = readM =<< getLine
print = putStrLn . show
