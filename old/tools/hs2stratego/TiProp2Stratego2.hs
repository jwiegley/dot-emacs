{-+
Knot-tying definitions for the type decorated base+property syntax to
Stratego translation.
-}
module TiProp2Stratego2 where
import TiPropDecorate(TiDecl(..),TiExp(..),
		      TiAssertion(..),OTiAssertion(..),TiPredicate(..))
import PropSyntax(prop,mapHsIdent)
import BaseStruct2Stratego2
import PropStruct2Stratego2
import Prop2Stratego2(transType,transContext,transTlhs,transQType)
import TiBase2Stratego2
import qualified Base2Stratego2 as B
import StrategoDecl
import TiClasses(fromDefs)
import Parentheses -- needed for pattern matching. Grr!!

transDecs ds = transDecs' (fromDefs ds)
transDecs' ds = concatMap transDec ds

transDec (Dec d) =
    prop (transD transId transExp transPat transLocalDecs transType transContext transTlhs)
         ((:[]) . transPD transId transOAssertion transPredicate)
         d

transExp e =
  case e of
    Exp e -> transE transId transExp transPat transLocalDecs transType transContext e
    TiSpec i _ _ -> transEId (mapHsIdent transId i)
    TiTyped e _ -> transExp e

transOAssertion (OA is ds a) = transAssertion a -- !!!

transAssertion (PA a) =
    transPA transId transExp transQType transAssertion transPredicate
            a

transPredicate (PP p) =
    transPP transId transExp B.transPat transQType transAssertion transPredicate
            p

transLocalDecs ds = concatMap transLocalDec (fromDefs ds)
transLocalDec d = [def|Def (P def)<-transDec d]
                  -- silently ignores unimplemented things!!!
