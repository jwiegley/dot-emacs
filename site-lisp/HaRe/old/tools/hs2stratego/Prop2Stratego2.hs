{-+
Knot-tying definitions for the base+property syntax to Stratego translation.
-}

module Prop2Stratego2 where
import BaseStruct2Stratego2(transP,transD,transE,transT,transTp,transTa,transId,not_supported)
import PropStruct2Stratego2(transPD,transPA,transPP,transQ)
import PropSyntax
import StrategoDecl
import Parentheses -- needed for pattern matching. Grr!!

--transPat :: PrintableOp i => HsPatI i -> P
transPat (Pat p) = transP transId transPat p

rmIgnored = filter notIgnored
  where
    notIgnored (Ignored _) = False
    notIgnored _ = True

transDecs ds = concatMap transDec ds

--transDec :: (IsSpecialName i,PrintableOp i) => HsDeclI i -> D
transDec (Dec d) =
    prop (transD transId transExp transPat transLocalDecs transType transContext transTlhs)
         ((:[]) . transPD transId transAssertion transPredicate)
         d

--transExp :: HsExp -> E
transExp (Exp e) =
    transE transId transExp transPat transLocalDecs transType transContext e

transAssertion (PA a) =
    transPA transId transExp transQType transAssertion transPredicate
            a

transPredicate (PP p) =
    transPP transId transExp transPat transQType transAssertion transPredicate
            p

transType (Typ t) = transT transId transType t
transContext ts = map transType ts

transQType qt = transQ transContext transType qt

--bad x = error "Base2Stratego: not yet"


transLocalDecs ds = concatMap transLocalDec ds
transLocalDec d = [def|Def (P def)<-transDec d]
                  -- silently ignores unimplemented things!!!

transTlhs (Typ t) = transTp transId transTlhs transTarg t
  where
    transTarg (Typ t) = transTa transId t
