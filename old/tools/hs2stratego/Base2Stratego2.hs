module Base2Stratego2 where
import BaseStruct2Stratego2
import Syntax(HsPatI(..))

transPat (Pat p) = transP transId transPat p
