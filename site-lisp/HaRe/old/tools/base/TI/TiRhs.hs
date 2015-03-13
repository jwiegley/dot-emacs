module TiRhs where
--import HasBaseStruct
import BaseSyntaxStruct
import TI
--import TiPrelude(tBool)
import MUtils
--import PrettyPrint -- debug

instance (--Printable i, -- debug
          TypeCon i,Fresh i,TypeCheck i e (Typed i e'),HasTypeAnnot i e')
      => TypeCheck i (HsRhs e) (Typed i (HsRhs e')) where
  tc = tcRhs

tcRhs rhs =
  case rhs of
    HsBody e -> emap HsBody # tc e
    HsGuard gds -> emap HsGuard # tcGds gds

tcGds gds =
  do gds':>:ts' <- unzipTyped # mapM tcGd gds
     t <- allSame ts'
     gds'>:t

tcGd (s,e1,e2) =
  posContext s $
  do e1':>:t1' <- tc e1
     tBool <- getBoolType
     t1'=:=tBool
     e2':>:t2' <- tc e2
     (s,e1',typeAnnot e2' t2')>:t2'
