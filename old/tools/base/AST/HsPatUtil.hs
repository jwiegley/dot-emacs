module HsPatUtil where

import HsPatStruct
import HsPatMaps(mapPI,accP)
import HsIdent({-getHSName,-}HsIdentI(..))
--import HsAssoc
import HasBaseStruct(basestruct)
import SpecialNames(tuple_name)

-- a generic way to examine patterns
isPVar p =
  case basestruct p of
    Just (HsPId (HsVar x))  -> Just x
    _                       -> Nothing

isIrrPat p =
  case basestruct p of
    Just (HsPIrrPat p)  -> Just p
    _                   -> Nothing


isWildCardPat p =
  case basestruct p of
    Just HsPWildCard    -> True
    _                   -> False

isAsPat p =
  case basestruct p of
    Just (HsPAsPat i p) -> Just (i,p)
    _                   -> Nothing


{-
isConPat p = 
  case basestruct p of
    Just bp ->
      case bp of
	HsPId (HsCon c) -> Just (c,[])
	HsPInfixApp p1 (HsCon c) p2 -> Just (c,[p1,p2])
	HsPApp c ps -> Just (c,ps)
	HsPTuple ps -> Just (tuple_name (length ps),ps)
        ...
-}
    

{- Obsolete...
-- Find all of the free identifiers (vars and cons) in an P structure:
freeIdentsP fiP p = 
  case p of 
    HsPId n -> [n]
    HsPAsPat nm p    -> HsVar nm:fiP p
    _                -> accP (++) [] (mapPI id fiP p)


reassociateP isinfix make undo rap env (HsPInfixApp a op1 b) =
    let f  = getHSName op1
        a' = rap env a
    in
        if isinfix a' then
	    let (op2, c, d) = undo a'
                g           = getHSName op2
	    in
                if (getPrec env f) > (getPrec env g) || 
		   ((getPrec env f == getPrec env g) && 
                     (getAssoc env f == HsAssocRight && 
                      getAssoc env g == HsAssocRight))
                then
		    HsPInfixApp c op2 (rap env (make d op1 b))
		else
		    HsPInfixApp a' op1 (rap env b)
	else
            HsPInfixApp a' op1 b
reassociateP isinfix make undo rap env p = mapPI id (rap env) p
-}
