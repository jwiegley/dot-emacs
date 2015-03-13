{-+
Auxiliary E structure functions.
-}

module HsExpUtil where

import HsExpStruct
import HsIdent
import SrcLoc1(SrcLoc)
--import HsAssoc
import HsExpMaps(mapEI, accEI)
import MUtils(( # ))

-- Auxiliary type used during parsing&printing, not part of the abstract syntax:
data HsStmtAtom e p ds
    = HsGeneratorAtom SrcLoc p e
    | HsQualifierAtom e
    | HsLetStmtAtom ds
    | HsLastAtom e
      deriving (Eq, Show) 

atoms2Stmt [HsQualifierAtom e]        = return (HsLast e)
atoms2Stmt (HsGeneratorAtom s p e : ss) = HsGenerator s p e # atoms2Stmt ss
atoms2Stmt (HsLetStmtAtom ds : ss)    = HsLetStmt ds # atoms2Stmt ss
atoms2Stmt (HsQualifierAtom e : ss)   = HsQualifier e # atoms2Stmt ss
atoms2Stmt _ = fail "last statement in a 'do' expression must be an expression"

getStmtList (HsGenerator l p e s) = HsGeneratorAtom l p e : getStmtList s
getStmtList (HsQualifier e s)   = HsQualifierAtom e : getStmtList s
getStmtList (HsLetStmt ds s)    = HsLetStmtAtom ds : getStmtList s
getStmtList (HsLast e)          = [HsLastAtom e]

isHsIdVar e =
  case e of
    HsId (HsVar n) -> Just n
    _ -> Nothing

{-
isPatternE iscon isvar pef pe =
  case pe of 
    HsId (HsVar n)              -> True
    HsTuple es                  -> all pef es
    HsWildCard                  -> True
    HsApp e1 e2 | iscon e1      -> pef e2
		| isvar e1      -> False
		| otherwise     -> pef e1 && pef e2
    HsList es                   -> all pef es
    HsInfixApp e1 (HsCon op) e2 -> pef e1 && pef e2
    HsParen e                   -> pef e   
    HsAsPat n e                 -> pef e
    HsRecConstr con fields      -> True
    _                           -> False
-}

{-
isFundefLhsE pef fdf pe p =
  case pe of  
    HsParen e                -> fdf e p
    HsId (HsVar n)           -> p
    HsApp l r                -> pef r && fdf l True
    HsInfixApp l (HsVar n) r -> pef l && pef r
    _                        -> False
-}

{-+
Finds all of the free variables in an E structure.
-}
{-
freeVarsE fve e = 
  case e of 
    HsId (HsVar n) -> [n]
    _              -> accEI (const id) (++) (++) (++) (++) (++)
                           (mapEI id fve (const []) (const [])
			             (const []) (const [])
			    e)
		    []
-}

{- Obsolete...
reassociateE isinfix make undo rae rap rads env (HsInfixApp a op1 b) =
    let f  = getHSName op1
        a' = rae env a
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
		    HsInfixApp c op2 (rae env (make d op1 b))
		else
		    HsInfixApp a' op1 (rae env b)
	else
            HsInfixApp a' op1 b
reassociateE isinfix make undo rae rap rads env e =
    mapEI id (rae env) (rap env) (rads env) id id e
-}

{-
removeParensE make rp e = 
  case e of 
    HsParen e' -> rp e'
    _          -> make $ mapEI id rp id id id id e
-}
