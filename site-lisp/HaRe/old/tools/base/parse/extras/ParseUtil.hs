-- $Id: ParseUtil.hs,v 1.8 2001/11/15 02:42:03 hallgren Exp $

{-

Utilities for the parser.

Author(s): Simon Marlow 1997, 1998;
           Emir Pasalic, Bill Harrison, Andrew Moran 2001

-}

module ParseUtil (--setInfix,          -- HsInfixDecl -> PM ()
		  splitTyConApp,     -- HsType -> PM (HsName, [HsType])
		  mkValDef,          -- HsExp -> SrcLoc -> HsRhs HsExp
		                     --   -> [HsDecl] -> PM HsDecl
                  mkFunDef,          -- HsExp -> SrcLoc -> HsRhs HsExp
                                     --   -> [HsDecl] -> PM HsDecl
                  mkFunDef',
                  expToPat)          -- HsExp -> PM HsPat
where

--import ParseMonad
--import Rewrite
import HsAssoc
import Syntax
import SyntaxUtil(isConE)
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
--splitTyConApp :: HsType -> PM (HsName, [HsType])
splitTyConApp t = split t []
    where
    --split :: HsType -> [HsType] -> PM (HsName, [HsType])
    split (Typ (HsTyApp t u)) ts = split t (u:ts)
    split (Typ (HsTyCon t))   ts = return (t, ts)
    split _                   _
        = fail "illegal data/newtype declaration"

--mkValDef :: HsExp -> SrcLoc -> HsRhs HsExp -> [HsDecl] -> PM HsDecl
mkValDef lhs sloc (HsBody b) wheres = 
    do { lpat <- expToPat lhs ;
	 return $ hsPatBind sloc lpat (HsBody b) wheres
       }
mkValDef lhs sloc (HsGuard gds) wheres = 
    do { lpat <- expToPat lhs ;
	 return $ hsPatBind sloc lpat (HsGuard gds) wheres
       }

--mkFunDef :: HsExp -> SrcLoc -> HsRhs HsExp -> [HsDecl] -> PM HsDecl
mkFunDef lhs sloc rhs wheres = 
    do { (fnamePat, ps) <- getFundefPats lhs ; 
	 case fnamePat of 
         Pat (HsPId (HsVar nm)) ->
              return $ hsFunBind sloc [HsMatch sloc nm ps rhs  wheres]
         _                      ->
              fail $ "invalid function name in:\n\n" ++ pp lhs
       }

mkFunDef' (nm,ps) sloc rhs wheres =
    hsFunBind sloc [HsMatch sloc nm ps rhs wheres]

--getFundefPats :: HsExp -> PM (HsPat, [HsPat])
getFundefPats (Exp pexp) = 
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
   _     -> fail $
	    "cannot use\n\n" ++ pp pexp ++
	   "\n\nas a function definition pattern."

--expToPat :: HsExp -> PM HsPat
expToPat l@(Exp lhexp)  = 
    case lhexp of 
      HsId (HsVar n) -> return $ hsPVar n
      HsId (HsCon n) -> return $ hsPCon n
      HsLit literal  -> return $ hsPLit literal
      HsNegApp  e    -> do { p <- expToPat e ; return $ hsPNeg p }
      HsLambda _ _   -> fail "lambdas not allowed in patterns."
      HsList es      -> do { ps <- sequence (map expToPat es) ;
			     return $ hsPList ps
			   }
      HsTuple es     -> do { ps <- sequence (map expToPat es) ;
			     return $ hsPTuple ps
			   }
      HsWildCard     -> return hsPWildCard
      HsIrrPat e     -> do { p <- expToPat e ; return $ hsPIrrPat p }
      HsAsPat nm e   -> do { p <- expToPat e ; return $ hsPAsPat nm p}
      HsApp l r | isConE l   -> 
                      do { let { Exp (HsId (HsCon n)) = l } ;
			   rp <- expToPat r ;
			   return $ hsPApp n [rp]
			 }
                | otherwise ->
                      do { lp <- expToPat l ;
                           rp <- expToPat r ;
                           case lp of 
                           Pat (HsPApp n ps) ->
			        return $ hsPApp n (ps ++ [rp])
                           _                 ->
			        fail $
			        "Cannot use:\n\n" ++
			        pp lhexp ++
			        "\n\n as a pattern."
                          }
      HsInfixApp l (HsCon n) r -> 
                       do { lp <- expToPat l ;
                            rp <- expToPat r ;
                            return $ hsPInfixApp lp (HsCon n) rp 
			  }
      HsParen e      -> expToPat e
      HsRecConstr con fields ->
                       do { pfs <- mapM fieldToPat fields ;
			    return $ hsPRec con pfs
			  }
      _              ->
          fail $ "ParseUtil.expToPat: not a valid/supported pattern:\n\n"
                       ++ pp lhexp
    where fieldToPat (HsFieldUpdate f e) = do { p <- expToPat e ;
						return $ HsPFieldPat f p
					      }
