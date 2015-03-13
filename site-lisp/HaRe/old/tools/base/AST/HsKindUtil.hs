-- $Id: HsKindUtil.hs,v 1.2 2005/05/04 06:05:27 hallgren Exp $

module HsKindUtil(matchK)

where

import HsKindStruct


matchK tx ty =
    case (tx, ty) of
    (Kstar,      Kstar)      -> Just []
    (Kfun x1 x2, Kfun y1 y2) -> Just [(x1, y1), (x2, y2)]
    (Kpred,      Kpred)      -> Just []
    (Kprop,      Kprop)      -> Just []
    (tx,         ty)         -> Nothing 
