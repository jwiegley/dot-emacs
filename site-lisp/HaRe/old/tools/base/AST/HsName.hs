{-# LANGUAGE DeriveDataTypeable #-}
module HsName where

import Data.Char(isAlpha,isUpper)
import Data.List(intersperse,isPrefixOf,isSuffixOf)
import PrettyPrint

import Data.Generics


{-+
Module Names
============

Modules are identified by their names. But since we want to support projects
containing more than one Main module, the module Main is instead identified
by the path to the file it resides in. (Perhaps there should be two different
types, one for module names, one for unique module identifiers.)
-}

data ModuleName
  = PlainModule String
  | MainModule FilePath
  deriving (Eq, Ord, Show, Read, Data, Typeable)

moduleName path "Main" = MainModule path
moduleName  _   s      = PlainModule s

plainModule s | s/="Main" = PlainModule s

isMainModule (MainModule _) = True
isMainModule _ = False

isHierarchical (PlainModule s) = '.' `elem` s
isHierarchical _ = False

sameModuleName "Main" (MainModule _)   = True
sameModuleName s      (PlainModule s') = s==s'
sameModuleName _ _ = False

fakeModule = PlainModule
  -- used by the type checker to create unique variables like t.1, t.2, d.1, d.2

noModule = fakeModule "noModule" -- not a valid module name

{-
instance Show ModuleName where
  showsPrec n (Module s) = showsPrec n s
instance Read ModuleName where
  readsPrec n s = [(Module m,r)|(m,r)<-readsPrec n s]
-}

{-
Identifiers
===========
-}
type Id = String


data HsName
    = Qual ModuleName Id
    | UnQual Id
      deriving (Eq, Ord, Show, Read, Data, Typeable)

hsUnQual = accHsName id

--- Map, Acc & Seq for the HsName functor --------------------------------------

mapHsName idf (Qual q id) = Qual q (idf id)
mapHsName idf (UnQual id) = UnQual (idf id)

accHsName idf (Qual q id) = idf id -- ??
accHsName idf (UnQual id) = idf id

--- Parsing pretty-printed module names ----------------------------------------

parseModuleName m =
    if "Main{-" `isPrefixOf` m && "-}" `isSuffixOf` m
    then MainModule . reverse . drop 2 . reverse . drop 6 $ m
    else PlainModule m

--- Pretty printing for HsName and Module --------------------------------------

instance Printable ModuleName where
    ppi (PlainModule m)   = ppi m
    ppi (MainModule path) = "Main"<>cmnt ("{-"<>path<>"-}")
    wrap                  = ppi

instance Printable HsName where
    ppi (Qual (PlainModule "Prelude") "[]") = ppi "[]" -- hack
    ppi (Qual (PlainModule "Prelude") "()") = ppi "()" -- hack
    ppi (Qual (PlainModule "Prelude") "(,)") = ppi "(,)" -- hack
    ppi (Qual (PlainModule "Prelude") "->") = ppi "(->)" -- hack
    ppi (Qual q id) = q <> '.' <> id
    ppi (UnQual id) = ppi id

    wrap n | isSymbolOp n = parens n
           | otherwise    = ppi n

instance PrintableOp HsName where
    isOp = isSymbolOp
    ppiOp n = if isAlphaOp n
	      then backQuotes n
	      else ppi n

isSymbolOp, isAlphaOp, isConOp :: HsName -> Bool
isSymbolOp = isSymbol . head . hsUnQual
isAlphaOp  = isAlpha  . head . hsUnQual
isConOp    =  (==':') . head . hsUnQual

ppInfixOp n = ppiOp n
ppInfixName n = ppiOp n

isSymbol c = elem c ":!#$%&*+./<=>?@\\^|-~"

--- Extra stuff for heirarchical module names ----------------------------------

splitQualName path = uncurry (Qual . moduleName path) . splitQualName'

{-
-- Haskell 98 version:
splitQualName' s = Qual (Module m) n
  where (m,'.':n) = break (=='.') s
-}

-- For the "hierachical module name" extension:
splitQualName' s = (m,n)
  where
    m = concat (intersperse "." (init parts))
    n = last parts
    parts = chop s

    chop "" = []
    chop ('.':s@(c:_)) = if isUpper c
			 then []:chop s
			 else []:[s]
    chop (c:s) =
	  case chop s of
	    [] -> [[c]]
	    s:ss -> (c:s):ss
