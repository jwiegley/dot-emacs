-----------------------------------------------------------------------------
-- |
-- Module      :  Pointfree
-- Copyright   :  (c) Jose Proenca 2005
-- License     :  GPL
--
-- Maintainer  :  jproenca@di.uminho.pt
-- Stability   :  experimental
-- Portability :  portable
--
-- A syntax of a general pointfree language.
--
-----------------------------------------------------------------------------

module Pointfree (
  -- * Data Type
  {-| Represents a pointfree language where:
        
        (1) products and sums are treated

        (2) base types are obtained and decomposed by the use of the /IN/ and
            /OUT/ constructors

        (3) recursion can be expressed by the point-fix function or by a paramorphism

        (4) free variables are called macros and represent known pointfree expressions
  -} 
  PFTerm (..),
  
  -- * Conversion of a "PFTerm" to an haskell expression
  pf2Exp

) where

import RefacUtils


data PFTerm = BANG             -- ^Constant function that returns Unit
          | ID                 -- ^Identity
          | APP                -- ^Apply
          | Curry PFTerm       -- ^Curry
          | PFTerm :.: PFTerm  -- ^Composition
          | PFTerm :\/: PFTerm -- ^Either
          | PFTerm :/\: PFTerm -- ^Split
          | FST                -- ^Point-free first
          | SND                -- ^Point-free second
          | INL                -- ^Point-free left injection
          | INR                -- ^Point-free right injection
          | IN HsExpP          -- ^Injection on a specified type
          | OUT HsExpP         -- ^Gets the functor
          | PARA HsExpP PFTerm -- ^Paramorphism
          | FIX                -- ^Fixed point function
          | Macro String       -- ^Macros of frequently used pointfree terms
            deriving Show
 

-- Implementation of a pointfree term on a HsExp
{- | Applies a tranformation from a 'PFTerm' to an expression of programatica's
     abstract tree. Note that the type information inside the /IN/, /OUT/ and /PARA/
     terms is represented as a programatica's expression @L::type@, where the @type@
     is the real type information.
-}
pf2Exp :: PFTerm -> HsExpI PNT

pf2Exp BANG = nameToExp "bang"
pf2Exp ID = prelVar "id"
pf2Exp APP = nameToExp "app"

pf2Exp (Curry t1)   = Exp $ HsApp (nameToExp "curry") (mbParen$ pf2Exp t1)
pf2Exp (t1 :.: t2)  = Exp (HsInfixApp  (mbParen$ pf2Exp t1)
                           (prelOp ".") (mbParen$ pf2Exp t2))
pf2Exp (t1 :\/: t2)  = Exp (HsInfixApp  (mbParen$ pf2Exp t1)
                           (nameToOp "\\/") (mbParen$ pf2Exp t2))
pf2Exp (t1 :/\: t2)  = Exp (HsInfixApp  (mbParen$ pf2Exp t1)
                           (nameToOp "/\\") (mbParen$ pf2Exp t2))

pf2Exp FST          = nameToExp "fst"
pf2Exp SND          = nameToExp "snd"
pf2Exp INL          = prelCon "Left"
pf2Exp INR          = prelCon "Right"


pf2Exp (IN typ)     = -- inN (_L::str)
    Exp (HsApp (nameToExp "inN") typ)--(Exp $ HsParen $ typedExp "_L" str))
pf2Exp (OUT typ)    = -- ouT (_L::str)
    Exp (HsApp (nameToExp "ouT") typ)--(Exp $ HsParen $ typedExp "_L" str))

pf2Exp (PARA typ t) = -- para (_L::str) t
    Exp (HsApp (Exp $ HsApp (nameToExp "para") typ)--(Exp $ HsParen $ typedExp "_L" str))
      (mbParen$ pf2Exp t))
pf2Exp FIX       = nameToExp "fix"

pf2Exp (Macro str)  = nameToExp str
 


---------------------------
--- auxiliary functions ---
---------------------------

-- nameToExp is imported from RefacUtils.hs
-- nameToExp str = Exp (HsId (HsVar (PNT (PN (UnQual str) (S loc0)) Value (N (Just loc0)))))

prelVar str = Exp (HsId (HsVar (PNT (PN (UnQual str) (G (PlainModule "Prelude") str (N (Just loc0)))) Value (N (Just loc0)))))

conToExp str = Exp (HsId (HsCon (PNT (PN (UnQual str) (S loc0)) Value (N (Just loc0)))))

prelCon str = Exp (HsId (HsCon (PNT (PN (UnQual str) (G (PlainModule "Prelude") str (N (Just loc0)))) Value (N (Just loc0)))))

-- | places parentisis in an expression only if it is necessary
--mbParen :: EI -> HsExp
mbParen e@(Exp (HsApp _ _)) = Exp $ HsParen e
mbParen e@(Exp (HsInfixApp _ _ _)) = Exp $ HsParen e
mbParen e@(Exp (HsCase _ _)) = Exp $ HsParen e
mbParen e@(Exp (HsLambda _ _)) = Exp $ HsParen e
mbParen x = x

prelOp str = (HsVar (PNT (PN (UnQual str) (G (PlainModule "Prelude") str (N (Just loc0)))) Value (N (Just loc0))))
nameToOp str = (HsVar (PNT (PN (UnQual str) (S loc0)) Value (N (Just loc0))))


typedExp strVar strType = Exp (HsExpTypeSig loc0 (nameToExp strVar) [] (Typ $ HsTyVar (PNT (PN (UnQual strType) (S loc0)) (Type (TypeInfo {defType = Nothing, constructors = [], fields = []})) (N (Just loc0)))))

