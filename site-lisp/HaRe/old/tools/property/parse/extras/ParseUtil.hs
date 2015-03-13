-- $Id: ParseUtil.hs,v 1.7 2001/11/06 06:33:37 hallgren Exp $

{-

Utilities for the parser.

Author(s): Simon Marlow 1997, 1998;
           Emir Pasalic, Bill Harrison, Andrew Moran 2001

-}

module ParseUtil (--setInfix,        -- HsInfixDecl -> PM ()
		  splitTyConApp,   -- HsType -> PM (HsName, [HsType])
                  mkQuant,         -- HsQuantifier -> [HsPat] -> HsExp -> HsExp
		  mkValDef,        -- HsExp -> SrcLoc -> HsRhs HsExp
		                   --   -> [HsDecl] -> PM HsDecl
                  mkFunDef,        -- HsExp -> SrcLoc -> HsRhs HsExp
                                   --   -> [HsDecl] -> PM HsDecl
                  expToPat)        -- HsExp -> PM HsPat
where

import ParseMonad
--import Rewrite
--import HsAssoc
import PropSyntax
import PropSyntaxUtil(isConE)
import PrettyPrint

{-
-- Update the infix environment with infix information from declaration.
setInfix (HsInfixDecl sl (HsFixity prec assoc) names) = 
  mapM (addToEnv prec assoc) names
  where 
      addToEnv prec HsAssocNone  n =
	  do { s <- getInfixEnv ;
	       setInfixEnv $ extend s (HsInfix HsAssocNone  prec n)
	     }
      addToEnv prec HsAssocRight n =
	  do { s <- getInfixEnv ;
	       setInfixEnv $ extend s (HsInfix HsAssocLeft  prec n)
	     }
      addToEnv prec HsAssocLeft  n =
	  do { s <- getInfixEnv ;
	       setInfixEnv $ extend s (HsInfix HsAssocRight prec n)
	     }
-}

splitTyConApp :: HsType -> PM (HsName, [HsType])
splitTyConApp t = split t []
    where
    split :: HsType -> [HsType] -> PM (HsName, [HsType])
    split (Typ (HsTyApp t u)) ts = split t (u:ts)
    split (Typ (HsTyCon t))   ts = return (t, ts)
    split _                   _
        = parseError "illegal data/newtype declaration"

mkQuant :: HsQuantifier -> [HsPat] -> HsExp -> HsExp
mkQuant q ps (e @ (Exp (Prop (HsQuant q' ps' e'))))
    | q == q'   = hsQuant q (ps ++ ps') e'
    | otherwise = hsQuant q ps e
mkQuant q ps e  = hsQuant q ps e

mkValDef :: HsExp -> SrcLoc -> HsRhs HsExp -> [HsDecl] -> PM HsDecl
mkValDef lhs sloc (HsBody b) wheres = 
    do { lpat <- expToPat lhs ;
	 return $ hsPatBind sloc lpat (HsBody b) wheres
       }
mkValDef lhs sloc (HsGuard gds) wheres = 
    do { lpat <- expToPat lhs ;
	 return $ hsPatBind sloc lpat (HsGuard gds) wheres
       }

mkFunDef :: HsExp -> SrcLoc -> HsRhs HsExp -> [HsDecl] -> PM HsDecl
mkFunDef lhs sloc rhs wheres = 
    do { (fnamePat, ps) <- getFundefPats lhs ; 
	 case fnamePat of 
         Pat (Base (HsPId (HsVar nm))) ->
              return $ hsFunBind sloc [HsMatch sloc nm ps rhs  wheres]
         _                      ->
              parseError $ "invalid function name in:\n\n" ++ pp lhs
       }


getFundefPats :: HsExp -> PM (HsPat, [HsPat])
getFundefPats (Exp (Base pexp)) = 
    case pexp of 
    HsId (HsVar nm) -> return (hsPVar nm, [])
    HsApp l r ->  
        do { (pv, ps) <- getFundefPats l ;
             p        <- expToPat r ;
             return (pv, ps ++ [p])
	   }
    HsInfixApp l (HsVar n) r -> 
        do { lp  <- expToPat l ;
             rp  <- expToPat r ;
             return (hsPVar n, [lp, rp])
	   }
    HsInfixApp l (HsCon n) r -> 
        do { lp  <- expToPat l ;
             rp  <- expToPat r ;
             return (hsPCon n, [lp, rp])
	   }
    HsParen e -> getFundefPats e
    _     -> parseError $
	     "cannot use\n\n" ++ pp pexp ++
	     "\n\nas a function definition pattern."
getFundefPats p =
    parseError $
    "cannot use\n\n" ++ pp p ++
    "\n\nas a function definition pattern."


expToPat :: HsExp -> PM HsPat
expToPat l@(Exp (Base lhexp))  = 
    case lhexp of 
      HsId (HsVar n) -> return $ hsPVar n
      HsId (HsCon n) -> return $ hsPCon n
      HsLit literal  -> return $ hsPLit literal
      HsNegApp  e    -> do { p <- expToPat e ; return $ hsPNeg p }
      HsLambda _ _   -> parseError "lambdas not allowed in patterns."
      HsList es      -> do { ps <- sequence (map expToPat es) ;
			     return $ hsPList ps
			   }
      HsTuple es     -> do { ps <- sequence (map expToPat es) ;
			     return $ hsPTuple ps
			   }
      HsWildCard     -> return hsPWildCard
      HsIrrPat e     -> do { p <- expToPat e ; return $ hsPIrrPat p }
      HsAsPat nm e   -> do { p <- expToPat e ; return $ hsPAsPat nm p}
      HsApp l r | isConE l  -> 
                        do { let { Exp (Base (HsId (HsCon n))) = l } ;
			     rp <- expToPat r ;
			     return $ hsPApp n [rp]
			   }
                | otherwise ->
                        do { lp <- expToPat l ;
                             rp <- expToPat r ;
                             case lp of 
                             Pat (Base (HsPApp n ps)) ->
			         return $ hsPApp n (ps ++ [rp])
                             _                 ->
			         parseError $
			         "Cannot use:\n\n" ++
			         pp lhexp ++
			         "\n\n as a pattern."
                           }
      HsInfixApp l (HsCon n) r -> 
                        do { lp <- expToPat l ;
                             rp <- expToPat r ;
                             return $ hsPInfixApp lp (HsCon n) rp 
			   }
      HsParen e                -> expToPat e
      HsRecConstr con fields   ->
                        do { pfs <- mapM fieldToPat fields ;
			     return $ hsPRec con pfs
			   }
      HsExpTypeSig _ e c t     ->
                        do { p <- expToPat e ;
                             return $ hsPatTypeSig p c t
                           }
      _                        ->
          parseError $ "ParseUtil.expToPat: not a valid/supported pattern:\n\n"
                       ++ pp lhexp
    where --fieldToPat (HsFieldBind f)     = return $ HsPFieldPun f
	  fieldToPat (HsFieldUpdate f e) = do { p <- expToPat e ;
						return $ HsPFieldPat f p
					      }
expToPat e  =
    parseError $ "ParseUtil.expToPat: not a valid/supported pattern:\n\n"
                 ++ pp e
