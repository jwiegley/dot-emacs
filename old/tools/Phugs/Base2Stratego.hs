{-+
Knot-tying definitions for the base syntax to Stratego translation.
-}

module Base2Stratego where
import BaseStruct2Stratego(transP,transD,transE,showId)
import Syntax(HsPatI(..),HsDeclI(..),HsExpI(..)) -- recursive base syntax

--transPat :: HsPat -> P
transPat (Pat p) = transP showId transPat p

transDecs ds = map transDec ds

--transDec :: HsDecl -> D
transDec (Dec d) = transD showId transExp transPat transDecs bad bad bad d

--transExp :: HsExp -> E
transExp (Exp e) = transE showId transExp transPat transDecs bad bad e

bad x = error "Base2Stratego: not yet"
