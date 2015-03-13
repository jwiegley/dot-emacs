-- $Id: Rewrite.hs,v 1.4 2001/07/30 05:57:46 hallgren Exp $

module Rewrite(rewriteModule, rewriteDecs, rewriteExp) where
{-
   This module supports rewriting of Haskell programs, mostly w.r.t., 
   operator fixity and association.  In particular, the function rewriteExp
   takes an operator environment and reassociates the infix expressions 
   as necessary.
-}

import Syntax
import SyntaxUtil
import HsAssoc(extend)
--import HsExpStruct 
--import HsDeclStruct
import HsModule
import HsName

rewriteModule env (HsModule m ex im decls) =
    HsModule m ex im (rewriteDecs env decls)

rewriteDecs env ds = map (rewriteDec env') ds
  where
    env' = foldl extend env fs
    fs = fixitiesD [d | Dec d <- ds]
  {- To be Haskell 98 compliant, this function also needs to reset the
     fixities of all names defined in ds without a fixity declaration in ds to
     the default, infixl 9.
     Also, for local definitions, the fixity environment should be in scope
     not only in the declarations themselves, but also in the expression(s)
     where the declarations are in scope...
   -}

rewriteDec env (Dec d) =
    Dec $ rewriteAllD (rewriteExp env)
	              (rewritePat env)
		      (rewriteDecs env)
		      d

rewriteExp env = reassociateExp env
rewritePat env = reassociatePat env

reassociateExp env (Exp e) =
    Exp $ reassociateE isInfixApp hsInfixApp getOpAndArgs
                       reassociateExp reassociatePat rewriteDecs env e

reassociatePat env (Pat p) =
    Pat $ reassociateP isPInfixApp hsPInfixApp getPOpAndArgs
                       reassociatePat env p

removeParens :: HsExp -> HsExp
removeParens (Exp e) = removeParensE Exp removeParens e
