-- $Id: Rewrite.hs,v 1.5 2001/10/19 04:10:12 hallgren Exp $

module Rewrite(rewriteModule, rewriteDecs, rewriteExp) where
{-
   This module supports rewriting of Haskell programs, mostly w.r.t., 
   operator fixity and association.  In particular, the function rewriteExp
   takes an operator environment and reassociates the infix expressions 
   as necessary.
-}

import PropSyntax
import PropSyntaxUtil
import HsExpStruct 
import HsDeclStruct
import HsModule
import HsAssoc
import HsPropStruct

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

rewriteDec env (PropDec pd) = PropDec $ rewritePD rewriteExp env pd
rewriteDec env (Dec d)      = Dec $ rewriteAllD (rewriteExp env)
			                        (rewritePat env)
			                        (rewriteDecs env) d

rewriteExp env e = reassociateExp env e
rewritePat env p = reassociatePat env p

reassociateExp env (Exp e)     =
    Exp $ reassociateE isInfixApp hsInfixApp getOpAndArgs
                       reassociateExp reassociatePat rewriteDecs env e
reassociateExp env (PropExp e) = PropExp $ mapPE (reassociateExp env) id e

reassociatePat env (PropPat pp) = PropPat pp -- no rewriting needed here...
reassociatePat env (Pat p)     =
    Pat $ reassociateP isPInfixApp hsPInfixApp getPOpAndArgs
                       reassociatePat env p


removeParens (Exp e)   = removeParensE Exp removeParens e

removeParens (PropExp e) = PropExp $ mapPE removeParens id e

