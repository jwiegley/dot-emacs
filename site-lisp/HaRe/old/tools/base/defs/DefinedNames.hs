{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies  #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}
module DefinedNames(module DefinedNames,module TypedIds) where
import TypedIds
import HsIdent
--import Maybe(mapMaybe)
import Recursive

{-+
This modules defines a class for extensible extraction of names
defined by declaration(s). Since the abstract syntax uses the same
type for top level declarations and the body of class definitions, we
need a separate function to extract the methods of a class.
-}

type TypedIdent i = (HsIdentI i,IdTy i)

class DefinedNames i def | def->i where
  definedNames :: def -> [TypedIdent i]

class ClassMethods i def | def->i where
  classMethods :: i -> Int -> def -> [TypedIdent i]

class ContextSize c where contextSize :: c -> Int

{-+
Some declarations have no explicit name in the concrete syntax, but can
be assigned an automatically generated name.
-}
class AddName i d | d->i where addName :: d -> d; addName=id

{-+
Default methods are part of class declarations in the Haskell syntax, but
after type checking we treat them as separate top-level entities with their
own names, so we need to be able to change their names...
-}
class MapDefinedNames i def | def->i where
  mapDefinedNames :: (i->i) -> def->def

{-+
Instances for collecting defined names from lists and pairs of things:
-}
instance DefinedNames i d => DefinedNames i [d] where
  definedNames = concatMap definedNames

instance ClassMethods i d => ClassMethods i [d] where
  classMethods c cnt = concatMap (classMethods c cnt)

instance AddName i d => AddName i [d] where
  addName = map addName

instance MapDefinedNames i d => MapDefinedNames i [d] where
  mapDefinedNames = map . mapDefinedNames

instance (DefinedNames i a, DefinedNames i b) => DefinedNames i (a,b) where
    definedNames (x,y)      = definedNames x ++ definedNames y
--    classMethods c (x,y)    = classMethods c x ++ classMethods c y

{-+
Auxiliary functions for extracting particular kinds of names:
-}
definedVars ds = filter isHsVar . definedValues $ ds -- hmm
definedValues' ds = filter (isValue.snd) . definedNames $ ds
definedValues ds = map fst . definedValues' $ ds
definedType tp = c where [(HsCon c,_)] = definedNames tp 

{-+
Auxiliary functions to simplify the definition of instances of #DefinedNames#:
-}
definedNamesRec x = definedNames (struct x)
classMethodsRec i cnt = classMethods i cnt . struct
mapDefinedNamesRec f = mapRec (mapDefinedNames f)
addNameRec x = mapRec addName x

value qn = (HsVar qn,Value)
-- con t defty cs n = (HsCon n,ConstrOf t defty cs)
con t defty n = (HsCon n,ConstrOf t defty)

field t tyinfo n = (HsVar n,FieldOf t tyinfo)
method c cnt ms n = (HsVar n,MethodOf c cnt ms)
-- tcon n defty cs fs = (HsCon n,Type defty cs fs)
tcon n tyinfo = (HsCon n, Type tyinfo)
classname c cnt methods = (HsCon c, Class cnt methods)

