{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances, UndecidableInstances, FunctionalDependencies, NoMonomorphismRestriction #-}
{-+
Since the type of identifiers is not hardwired in the type checker,
this module defines some type classes that capture what the type checker needs
to do with identifiers.
-}
module TiNames where
import Data.Char(isAlphaNum)
import HsIdent
import HsName(ModuleName)
import HsConstants(mod_Prelude)
import SrcLoc1(SrcLoc,srcFile,srcLoc)
import SrcLocPretty(shLineCol)
import PrettyPrint(Printable,pp)
import SpecialNames
import TypedIds(IdTy(..),HasIdTy(..))
import UniqueNames(PN)

type SrcName = String

class ValueId i where
  topName   :: Maybe SrcLoc -> ModuleName -> SrcName -> IdTy (PN String) -> i
  localVal' :: SrcName -> Maybe SrcLoc -> i
--instName  :: ModuleName -> SrcLoc -> i
  dictName' :: Int -> Maybe SrcLoc -> i
  superName :: i -> Int -> i
  defaultName :: i -> i

class HasIdTy n i => TypedId n i | i->n where
  idName :: i -> n

isCon i = 
  case idTy i of
    ConstrOf {} -> True
    _ -> False

dictName i = dictName' i Nothing
conName' s m n t ty = topName s m n (ConstrOf t ty)
conName m = conName' Nothing m
prelCon c = conName mod_Prelude c
localVal n = localVal' n Nothing
topVal' m n s = topName s m n Value
topVal m n = topVal' m n Nothing
prelVal' n = topVal' mod_Prelude n
prelVal n = prelVal' n Nothing

{-+ #instName# generates context-independent, unique names for instance
declarations. The module name is included so that the instance names remain
unique when mutually recursive groups of modules are combined into one module.
-}
instName m s inst =
    --topName (Just s) m ("inst__"++pp m++"_"++shLineCol s) Value
    topName (Just s) m ("inst__"++dots2uscore (pp m)++"_"++mangle (pp inst)) Value
  where
    -- A quick hack: !!!
    mangle = concatMap mangle1
    mangle1 c =
      case c of
        ' ' -> "_"
	'(' -> "_l_"
	')' -> "_r_"
	_ -> if isAlphaNum c then [c] else "_"++show (fromEnum c)

instName' modmap s = instName (modmap (srcFile s)) s

derivedInstName' modmap cl = derivedInstName m cl
  where
    s = srcLoc cl
    m = modmap (srcFile s)

derivedInstName m cl tn =
    topName (Just s) m ("derived__"++dots2uscore (pp m)++"_"++pp cl++"_"++n) Value
  where
    s = srcLoc cl
    ts = pp tn
    n = if all isAlphaNum' ts
	then ts
	else shLineCol s
    isAlphaNum' c = c `elem` "_'" || isAlphaNum c

-- For the annoying 'hierarchical' module name extension:
dots2uscore = map dot2uscore
dot2uscore '.' = '_'
dot2uscore c = c

class (HasSpecialNames i,IsSpecialName i) => TypeCon i where
  topType :: ModuleName -> SrcName -> i

prelType n = topType mod_Prelude n

class (Ord i,Printable i) => TypeVar i where
  tvar :: Int -> i
  ltvar :: SrcName -> i

class (TypeCon i,TypeVar i) => TypeId i

-- Prelude values and constructors
pv n = HsVar (prelVal n)
pc n = HsCon (prelVal n)
