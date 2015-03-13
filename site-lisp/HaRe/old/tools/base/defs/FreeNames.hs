{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances, UndecidableInstances, FunctionalDependencies, NoMonomorphismRestriction #-}
module FreeNames(module FreeNames,NameSpace(..)) where

import HsIdent
import TypedIds(NameSpace(..),namespace)
import Data.List(nub)
import MUtils(mapSnd)
import DefinedNames
import Recursive

{-+
This modules defines a class for extensible extraction of free names
from expressions, type expressions, etc. By free names, we mean names that
occur in an expression and need to be defined/introduced elsewhere. For
example, the constructors that appear in a pattern are considered free names,
while the variables in a pattern are considered defined names rather than
free names.

While it would make sense for method #freeNames# to return a set instead of
a list, there are currently some places in the code where the free names
are assumed to be listed in the order they appeared in the expression
(.e.g. in the definition of TiFreeNames.typeParams).
-}

type FreeName i = (HsIdentI i, NameSpace)

class Eq i => FreeNames i t | t -> i where
    freeNames :: t -> [FreeName i]

{-+
Instances for collecting free names from lists, pairs and sums of things:
-}
instance FreeNames i t => FreeNames i [t] where
    freeNames  = nub . concatMap freeNames

instance (FreeNames i a, FreeNames i b) => FreeNames i (a,b) where
    freeNames (x,y) = nub (freeNames x ++ freeNames y)

instance (FreeNames i a, FreeNames i b,FreeNames i c)
       => FreeNames i (a,b,c) where
    freeNames (x,y,z) = nub (freeNames x ++ freeNames y ++ freeNames z)

instance (FreeNames i a, FreeNames i b) => FreeNames i (Either a b) where
    freeNames = either freeNames freeNames

instance FreeNames i a => FreeNames i (Maybe a) where
  freeNames = maybe [] freeNames

{-+
Auxiliary functions:
-}
defs x         = mapSnd namespace . definedNames $ x
freeValues x   = map fst . filter ((==ValueNames).snd) . freeNames $ x

freeNamesRec x = freeNames (struct x)

freeCons x = filter (isHsCon.fst) . freeNames $ x
freeVars x = filter (isHsVar.fst) . freeNames $ x

istyvar (x,sp) = isHsVar x && sp==ClassOrTypeNames

-- utils ---------------------------------------

tcon = typ . HsCon
tvar = typ . HsVar
con = val . HsCon
var = val . HsVar

val x           = (x, ValueNames)
typ x           = (x, ClassOrTypeNames)

