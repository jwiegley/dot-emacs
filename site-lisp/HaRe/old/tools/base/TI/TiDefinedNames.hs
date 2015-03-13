module TiDefinedNames(
  module TiDefinedNames,DefinedNames(..),MapDefinedNames(..))
where
import DefinedNames hiding (definedType)
import Data.Maybe(mapMaybe,listToMaybe)
import HsIdent
import MUtils(( # ))

-- Defined to minic the instances of the deprecated class DefinedVars...
valueNames = mapMaybe valueName
valueName (n,t) =
  case t of
    Value      -> Just n
    Property   -> Just n
    Assertion  -> Just n
    _          -> Nothing

valuesNames' = mapMaybe valueName'
valueName' (n,t) =
  case t of
    Value       -> Just n
    Property   -> Just n
    Assertion  -> Just n
    ConstrOf {} -> Just n
    FieldOf  {} -> Just n
    MethodOf {} -> Just n
    _           -> Nothing

valueIdent (n,t) =
  case t of
    Value       -> Just (HsVar n)
    Property   -> Just (HsCon n)
    Assertion  -> Just (HsCon n)
    ConstrOf {} -> Just (HsCon n)
    FieldOf  {} -> Just (HsVar n)
    MethodOf {} -> Just (HsVar n)
    _           -> Nothing

typeNames = mapMaybe typeName
typeName (n,t) =
  case t of
    Class {} -> Just n
    Type {} -> Just n
    _       -> Nothing

typeIdent (n,t) =
  case t of
    Class {} -> Just (HsCon n)
    Type {} -> Just (HsCon n)
    _       -> Nothing

definedValueNames x = valueNames . definedNames $ x
definedTypeNames  x = typeNames  . definedNames $ x

definedType x = maybe err id (optDefinedType x)
  where err = error ("definedType "++show x)

optDefinedType x = listToMaybe . definedTypeNames $ x -- hmm

definedTypeName t = tn where HsCon tn = definedType t

optDefinedTypeName t = unCon # optDefinedType t
  where
    unCon (HsCon tn) = tn

definedNamesSplit x = (typeNames ns,valueNames ns)
  where ns = definedNames x

patternVars p = filter isHsVar (definedValueNames p)
