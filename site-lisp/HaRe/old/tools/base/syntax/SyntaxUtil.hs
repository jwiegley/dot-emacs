module SyntaxUtil(module SyntaxUtil,module HsConstants) where
import HsConstants
import Syntax
import PrettyPrint

-- Built-in type constructors/names

unit_tycon          = hsTyCon unit_tycon_name :: HsType
fun_tycon           = hsTyCon fun_tycon_name  :: HsType
list_tycon          = hsTyCon list_tycon_name :: HsType
tuple_tycon i       = hsTyCon $ tuple_tycon_name i :: HsType


-- Test functions (used by the parser)
isPatternExp :: HsExp -> Bool
isPatternExp (Exp pe) = isPatternE isConE isVarE isPatternExp pe

isFundefLhs :: HsExp -> Bool -> Bool
isFundefLhs (Exp pe) p = isFundefLhsE isPatternExp isFundefLhs pe p

isInfixApp :: HsExp -> Bool
isInfixApp (Exp (HsInfixApp _ _ _)) = True
isInfixApp _                        = False

isPInfixApp :: HsPat -> Bool
isPInfixApp (Pat (HsPInfixApp _ _ _)) = True
isPInfixApp _                         = False

isConE (Exp (HsId (HsCon _))) = True
isConE _                      = False

isVarE (Exp (HsId (HsVar _))) = True
isVarE _                      = False

isTyVar (Typ (HsTyVar _)) = True
isTyVar _                 = False


-- Extractor functions

getOpAndArgs :: HsExp -> (HsIdent, HsExp, HsExp)
getOpAndArgs (Exp (HsInfixApp a op b)) = (op, a, b)
getOpAndArgs e                         =
    error ("BaseSyntaxUtil.getOpAndArgs: not an infix application:\n\n"
	   ++ pp e ++ "\n")

getPOpAndArgs :: HsPat -> (HsIdent, HsPat, HsPat)
getPOpAndArgs (Pat (HsPInfixApp a op b)) = (op, a, b)
getPOpAndArgs p                         =
    error ("BaseSyntaxUtil.getPOpAndArgs: not an infix application:\n\n"
	   ++ pp p ++ "\n")

getTyVar (Typ (HsTyVar v)) = v
getTyCon (Typ (HsTyCon c)) = c

getTyName (Typ (HsTyVar v)) = v
getTyName (Typ (HsTyCon c)) = c


{-
-- Produces a nub'd list of type variable names in the list

namesTyp (Typ t) = namesT namesTyp t
namesT acct t = reverse $ accNamesT t []
    where accNamesT (HsTyVar n) ans | n `elem` ans = ans
				    | otherwise    = n : ans
          accNamesT t           ans = accT acct t ans
-}

