{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE MultiParamTypeClasses, OverlappingInstances, UndecidableInstances, FunctionalDependencies, NoMonomorphismRestriction #-}
module TiHsName where
import HsName
import HsConstants()
import SrcLoc1
import SpecialNames
import TiNames
import TiFresh
import MUtils

instance ValueId HsName where
  topName s m n ty = UnQual n -- or Qual m n?
  localVal' n _ = UnQual n
--instName m s = UnQual (instName m s)
  dictName' n _ = fakeQual "d" (show n)
  superName q k = mapHsName (flip superName k) q
  defaultName = mapHsName defaultName

instance TypeCon HsName where topType = Qual
instance TypeVar HsName where
  tvar = fakeQual "t" . show
  ltvar = UnQual

fakeQual s = Qual (fakeModule s)

instance TypeId HsName

instance Fresh HsName where fresh = tvar # fresh

instance IsSpecialName Id -- dummy
instance HasSpecialNames Id -- dummy

instance TypeCon Id where topType m n = n

instance ValueId Id where
  topName s m n ty = n
--instName m (SrcLoc f l c) = "inst__"++show l++"_"++show c
  superName n k = "super"++show k++"_"++n
  defaultName n = if isSymbol (head n)
		  then "$--"++n
		  else "default__"++n
