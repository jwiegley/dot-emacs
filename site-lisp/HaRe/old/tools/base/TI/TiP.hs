module TiP where
import HasBaseStruct
import BaseSyntaxStruct
import TI
import TiLit(tcLit)
import TiFields(tcFieldsPat)
--import TiPrelude
import MUtils

instance HasId i (PI i p) where
  ident = HsPId
  isId (HsPId x) = Just x
  isId _ = Nothing
{-
instance (Fresh i,TypeId i,ValueId i,
          TypeCheck i inp (Typed i outp),HasLit outp,
	  HasTypeApp i outp, HasBaseStruct outp (PI i outp))
	 => TypeCheck i (PI i inp) (Typed i outp) where tc = tcP
-}
tcP p =
  case p of
    HsPId n                -> inst n
--  HsPLit l               -> emap hsPLit # tcLit0 l
    HsPLit s l             -> tcLitP s l
    HsPNeg s l             -> instPrel_srcloc s "negate" `tapp` tcLitP s l
    HsPSucc s n l          -> instPrel_srcloc s "+" `tapp` inst (HsVar n) `tapp` tcLitP s l
    HsPInfixApp x op z     -> instCon op `tapp` tc x `tapp` tc z
    HsPApp nm ps           -> tcPApp nm ps
    HsPTuple s ps          -> typedTuple =<< mapM tc ps
    HsPList  s ps          -> tcList =<< mapM tc ps
    HsPParen p             -> emap hsPParen # tc p
    HsPRec c fields        -> tcFieldsPat c fields
    HsPAsPat nm p          -> tcAsPat nm p
    HsPWildCard            -> (hsPWildCard:>:) # tfresh
    HsPIrrPat p            -> emap hsPIrrPat # tc p
  where
    tcLitP s = tcLit (hsPLit s) s

tcPApp con ps = foldl tapp (instCon con) (map tc ps)

instCon c = inst (HsCon c)

tcAsPat x p =
  do tx <- varinst x
     p' :>: tp <- tc p
     tx =:= tp
     hsPAsPat x p' >: tp

-- binary version of HsPApp (only for constructor applications):
pApp p1 p2 =
  case p1 of
    HsPId (HsCon c) -> HsPApp c [p2]
    HsPApp c ps -> HsPApp c (ps++[p2])
--  _ -> error ("pApp "++show p1)
