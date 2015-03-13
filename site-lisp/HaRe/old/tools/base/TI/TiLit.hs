-- Type inference for literals.
module TiLit where
import BaseSyntaxStruct
--import HasBaseStruct
--import TiPrelude
import TI
import MUtils
{-
instance (TypeId i,ValueId i,Fresh i,
          --HasBaseStruct e (EI i e' p ds t c),
	  HasLit e,
	  HasTypeApp i e)
       => TypeCheck i HsLiteral (Typed i e) where
  tc = tcLit
-}
-- Overloaded literals:
tcLit r s l =
  case l of
    HsInt  _ -> instPrel_srcloc s "fromInteger" `tapp` tl
    HsFrac _ -> instPrel_srcloc s "fromRational" `tapp` tl
    _ -> tl
  where
    tl = emap r # tcLit0 l

-- Non-overloaded literals:
tcLit0 lit = do t <- tLit lit
                lit >: t

-- Types of non-overloaded literals:
tLit lit =
  case lit of
    HsInt    _ -> prelTy "Integer"
    HsChar   _ -> prelTy "Char"
    HsString _ -> prelTy "String"
    HsFrac   _ -> prelTy "Rational"
    -- + extensions...
