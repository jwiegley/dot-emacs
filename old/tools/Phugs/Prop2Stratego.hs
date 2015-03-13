{-+
Knot-tying definitions for the base+property syntax to Stratego translation.
-}

module Prop2Stratego where
import BaseStruct2Stratego(transP,transD,transE,showId)
import PropStruct2Stratego(transPD,transPA,transPP)
import PropSyntax --hiding (D,P,E) -- recursive base+prop syntax
import PrettyPrint
import SpecialNames
import StrategoAST(D,P,E)

transPat :: PrintableOp i => HsPatI i -> P
transPat (Pat p) = transP showId transPat p

transDecs ds = map transDec ds

transDec :: (IsSpecialName i,PrintableOp i) => HsDeclI i -> D
transDec (Dec d) =
    prop (transD showId transExp transPat transDecs bad bad bad)
         (transPD showId transAssertion transPredicate)
         d

--transExp :: HsExp -> E
transExp (Exp e) = transE showId transExp transPat transDecs bad bad e

transAssertion (PA a) =
   transPA showId transExp bad transAssertion transPredicate
           a

transPredicate (PP p) =
   transPP showId transExp transPat bad transAssertion transPredicate
           p

bad x = error "Base2Stratego: not yet"
