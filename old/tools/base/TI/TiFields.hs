module TiFields where
import HasBaseStruct
import BaseSyntaxStruct
import HsFieldsStruct
import TI
import MUtils
--import SpecialNames -- debug

instance (--IsSpecialName i, -- debug
	  ValueId i,TypeVar i,Fresh i,TypeCheck i e (Typed i e2))
      => TypeCheck i (HsFieldsI i e) (Typed i (HsFieldsI i e2)) where
  tc fs=
    do fs:>:ts <- unzipTyped # mapM tc fs
       t <- allSame ts
       fs>:t

instance (--IsSpecialName i, -- debug
          ValueId i,TypeVar i,Fresh i, TypeCheck i e (Typed i e2))
      => TypeCheck i (HsFieldI i e) (Typed i (HsFieldI i e2)) where
  tc=tcHsField

tcHsField (HsField f e) =
  do ft <- inst_field (HsVar f)
     e':>:et <- tc e
     r <- tfresh
     hsTyFun r et =:= ft
     HsField f e'>:r

tcFieldsPat c = tcFieldsCon' hsPRec c
tcFieldsCon s c = tcFieldsCon' (hsRecConstr s) c

tcFieldsCon' appf c = tcFields appf bM
  where
    bM = do tcon <- inst_field (HsCon c)
	    c>:resultType tcon
    resultType (Typ t) =
      case t of
        HsTyFun _ t -> resultType t
	_ -> Typ t

tcFieldsUpd s bM = tcFields (hsRecUpdate s) bM

tcFields c bM fields =
  do b:>:bt <- bM
     fs:>:ft <- tc fields
     bt=:=ft
     c b fs>:bt
