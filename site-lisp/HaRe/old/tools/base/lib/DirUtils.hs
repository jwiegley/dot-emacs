{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances, UndecidableInstances, FunctionalDependencies, NoMonomorphismRestriction #-}
module DirUtils where
import Prelude hiding (catch,ioError)
import MUtils
import Data.List(isSuffixOf,nub)
import AbstractIO
import PathUtils(pathSep)

optCreateDirectory d = unlessM (doesDirectoryExist d) (createDirectory d)

getModificationTimeMaybe path = maybeM (getModificationTime path)
{-
  do ifM (doesFileExist path)
         (Just # getModificationTime path)
	 (return Nothing)
-}

-- GHC deficiency workaround:
getModificationTime' path = getModificationTime path `catch` handle
  where
    handle err = if isDoesNotExistError err
		 then fail $ "Missing: "++path
		 else ioError err

latestModTime paths = maximum # mapM getModificationTime' paths


-- Remove a directory and its contents:
rmR = system . unwords . ("rm -rf":)
			  

-- Expand directory names to all the Haskell files (.hs & .lhs) in that
-- directory:
expand fs = concat # mapM expand1 (nub fs)
expand1 f =
  do isdir <- doesDirectoryExist f
     if isdir
      then do fs <- getDirectoryContents f
              return [f++[pathSep]++f'|f'<-fs,haskellSuffix f']
      else return [f]

haskellSuffix f = ".hs" `isSuffixOf` f || ".lhs" `isSuffixOf` f

{-
-- Recursively collect Haskell files from subdirectories:
recurse = recurse' "" . nub

recurse' path fs = concat # mapM (recurse1 path) fs

recurse1 path f =
  do let path' = extend path f
     isdir <- doesDirectoryExist path'
     if isdir
      then if okDir f
           then do fs <- getDirectoryContents path'
	           recurse' path' [f|f<-fs,f `notElem` [".",".."]]
	   else return []
      else if haskellSuffix f
	   then return [path']
	   else return []

okDir f = f `notElem` ["objs","CVS","hi","tests","old","spec"]

extend "" f = f
extend "." f = f
extend d f = d++"/"++f
-}
