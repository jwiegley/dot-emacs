{-# LANGUAGE DeriveDataTypeable  #-}
module SrcLoc1(
    SrcLoc(..), -- source location data type
    HasSrcLoc(..), -- source location class
    srcFile,
    loc0)       -- :: SrcLoc, initial dummy location
  where

import Data.Generics

data SrcLoc = SrcLoc {srcPath::FilePath,
		      srcChar,srcLine,srcColumn:: !Int }
  deriving (Eq,Ord, Data, Typeable)

instance Show SrcLoc where
   showsPrec p (SrcLoc f n l c) = showsPrec p (f,n,l,c)

instance Read SrcLoc where
   readsPrec p s = [(SrcLoc f n l c,r)|((f,n,l,c),r)<-readsPrec p s]

class HasSrcLoc syntax where 
  srcLoc :: syntax -> SrcLoc

srcFile x = srcPath (srcLoc x)

loc0 = SrcLoc "__unknown__" 0 0 0

instance HasSrcLoc s => HasSrcLoc [s] where
  srcLoc [] = loc0
  srcLoc (x:xs) = srcLoc x

instance HasSrcLoc SrcLoc where srcLoc = id
