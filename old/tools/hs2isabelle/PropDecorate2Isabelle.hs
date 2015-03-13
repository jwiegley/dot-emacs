{-+
Knot-tying definitions for the base+property+typeinfo syntax to Isabelle
translation.
-}

module PropDecorate2Isabelle where
import BaseStruct2Isabelle(transP,transD,transE,transId)
import PropStruct2Isabelle(transPD,transPA,transPP)
import Prop2Isabelle(transQType,transType,transContext)
import qualified Prop2Isabelle as P2S(transPat)
import TiPropDecorate
import PropSyntaxStruct(prop)
import HasBaseStruct(hsId,hsPId)
import TiDecorate(TiPat(..))
import TiClasses(fromDefs,toDefs)
import IsabelleDecl

--transPat :: PrintableOp i => HsPatI i -> P
transPat (Pat p) = transP transId transPat p
transPat (TiPApp p1 p2) = transPat p2 -- !!!
transPat (TiPSpec i _ _) = transPat (hsPId i)
transPat (TiPTyped e t) = transPat e

rmIgnored = filter notIgnored
  where
    notIgnored (Ignored _) = False
    notIgnored _ = True

transDecs ds = map transDec ds

--transDec :: (IsSpecialName i,PrintableOp i) => HsDeclI i -> D
transDec (Dec d) =
    prop (transD transId transExp transPat transLocalDecs transType transContext transType)
         (transPD transId transOAssertion transPredicate)
         d

--transExp :: HsExp -> E
transExp (Exp e) =
    transE transId transExp transPat transLocalDecs transType transContext e
transExp (TiSpec i _ _) = transExp (hsId i)
transExp (TiTyped e t) = transExp e

transOAssertion (OA xs ds a) = {- ... -} transAssertion a -- !!!

transAssertion (PA a) =
  transPA transId transExp transQType transAssertion transPredicate
          a

transPredicate (PP p) =
  transPP transId transExp P2S.transPat transQType transAssertion transPredicate
          p

--transType (Typ t) = transT transId transType t
--transContext ts = map transType ts

--transQType qt = transQ transContext transType qt

--bad x = error "Base2Isabelle: not yet"


transLocalDecs ds = concatMap transLocalDec (fromDefs ds)
transLocalDec d =
  case transDec d of
    Def (P def) -> [def]
    _ -> [] -- silently ignores unimplemented things!!!
