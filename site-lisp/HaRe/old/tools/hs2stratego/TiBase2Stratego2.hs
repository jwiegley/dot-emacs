module TiBase2Stratego2 where
import HsIdent(mapHsIdent)
import TiDecorate(TiPat(..))
import BaseStruct2Stratego2(transP,transPId,transId,not_supported)
import StrategoPattern(Pattern(ConstrPat))

transPat p =
  case p of
    Pat p -> transP transId transPat p
    TiPSpec i _ _ -> transPId (mapHsIdent transId i)
    TiPApp p1 p2 -> transPat p1 `pApp` transPat p2
    TiPTyped p _ -> transPat p
    _ -> not_supported "Pattern" p
  where
    pApp (ConstrPat (c,ps)) p =  ConstrPat (c,ps++[p])
    pApp _ _ = not_supported "Pattern" p
