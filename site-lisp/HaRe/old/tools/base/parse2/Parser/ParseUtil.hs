{-
Utilities for the parser.

Author(s): Simon Marlow 1997, 1998;
           Emir Pasalic, Bill Harrison, Andrew Moran 2001
           Thomas Hallgren 2001, 2002
-}

module ParseUtil (chkTypeLhs,        -- ([HsType],HsType) -> m ([HsType],HsType)
		  splitTyConApp,     -- HsType -> m (HsName, [HsType])
		  mkValDef,          -- HsExp -> SrcLoc -> HsRhs HsExp
		                     --   -> [HsDecl] -> m HsDecl
                  mkFunDef,          -- HsExp -> SrcLoc -> HsRhs HsExp
                                     --   -> [HsDecl] -> m HsDecl
                  mkFunDef',
                  expToPat,          -- HsExp -> m HsPat
                  hsName2modName)    -- HsName -> ModuleName
                       -- Monad m => ...
		       -- The monad is used for error handling only
where

--import HsAssoc
import Syntax
--import SyntaxUtil(isConE)
import HsName
import SourceNames
import PrettyPrint
--import HsConstants(plus_name)
import MUtils

-- The LHSs of data/newtype/class declaration is parsed like a ctype (c=>t),
-- so this additional check is needed to ensure that they are well formed.
chkTypeLhs ct@(ctx,t) =
  do (c,as) <- splitTyConApp t
     if all isTyVar as
       then return ct
       else fail "bad lhs in data/newtype/class declaration"
  where
    isTyVar (Typ (HsTyVar _)) = True
    isTyVar _ = False

--splitTyConApp :: HsType -> m (HsName, [HsType])
splitTyConApp t = split t []
    where
    --split :: HsType -> [HsType] -> m (HsName, [HsType])
    split (Typ (HsTyApp t u)) ts = split t (u:ts)
    split (Typ (HsTyCon t))   ts = return (t, ts)
    split _                   _
        = fail "illegal data/newtype declaration"

--mkValDef :: HsExp -> SrcLoc -> HsRhs HsExp -> [HsDecl] -> m HsDecl
mkValDef lhs sloc (HsBody b) wheres = 
    do { lpat <- expToPat lhs ;
	 return $ hsPatBind sloc lpat (HsBody b) wheres
       }
mkValDef lhs sloc (HsGuard gds) wheres = 
    do { lpat <- expToPat lhs ;
	 return $ hsPatBind sloc lpat (HsGuard gds) wheres
       }

--mkFunDef :: HsExp -> SrcLoc -> HsRhs HsExp -> [HsDecl] -> m HsDecl
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

--getFundefPats :: HsExp -> m (HsPat, [HsPat])
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

expToPat l@(Exp lhexp)  = 
    case lhexp of 
      HsId (HsVar n) -> return $ hsPVar n
      HsId (HsCon n) -> return $ hsPCon n
      HsLit s literal -> return $ hsPLit s literal
      HsNegApp s e   -> do p <- expToPat e
			   case p of
			     Pat (HsPLit s l) -> return (hsPNeg s l)
			     _ -> fail "only literals can be negated in patterns"
      HsLambda _ _   -> fail "lambdas not allowed in patterns."
      HsList es      -> do { ps <- sequence (map expToPat es) ;
			     return $ hsPList loc0 ps -- !! loc0
			   }
      HsTuple es     -> do { ps <- sequence (map expToPat es) ;
			     return $ hsPTuple loc0 ps -- !! loc0
			   }
      HsWildCard     -> return hsPWildCard
      HsIrrPat e     -> do { p <- expToPat e ; return $ hsPIrrPat p }
      HsAsPat nm e   -> do { p <- expToPat e ; return $ hsPAsPat nm p}
      HsApp (Exp (HsId (HsCon n))) r -> 
                      do { rp <- expToPat r ;
			   return $ hsPApp n [rp]
			 }
      HsApp l r -> 
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
                            return $ hsPInfixApp lp n rp 
			  }
      HsInfixApp ne (HsVar (SN op _)) ke | op==UnQual "+" -> -- n+k patterns!!!
                     do np <- expToPat ne
                        kp <- expToPat ke
                        case (np,kp) of
                          (Pat (HsPId (HsVar n)),Pat (HsPLit s l)) ->
                               return $ hsPSucc s n l
                          _ -> fail$ pp $ "Mailformed n+k pattern:"<+>lhexp

      -- HsParen e      -> expToPat e
      HsParen e      -> do
                           e1 <- expToPat e
                           return (Pat (HsPParen e1))

      HsRecConstr s con fields ->
                       do { pfs <- mapM fieldToPat fields ;
			    return $ hsPRec con pfs
			  }
      _              ->
          fail $ "ParseUtil.expToPat: not a valid/supported pattern:\n\n"
                       ++ pp lhexp
    where fieldToPat (HsField f e) = HsField f # expToPat e
