module HsPropStruct where

import HsIdent(HsIdentI)
import SrcLoc

-------- Properties --------------------------------------------------------

data Quantifier = All | Exist deriving (Eq, Show)

-- Although we do not expect to extend these, so we don't tie the recursive
-- knots immmediately, to be consistent with the programming style used for
-- the base syntax.

-- Declarations extensions:
data PD i pa pp
  = HsAssertion SrcLoc (Maybe i) pa
  | HsPropDecl SrcLoc i [HsIdentI i] pp
  deriving (Eq, Show)

data PropOp = Conj | Disj | Imp | Equiv deriving (Eq,Show)

-- Property assertions:
data PA i e t pa pp
  = Quant Quantifier i (Maybe t) pa
--  | PropId i -- just a special case of PropApp
  | PropApp i [t] [PredArg e pp] -- type arguments are added by the type checker
  | PropNeg pa
  | PropOp PropOp pa pa
  | PropEqual e e
  | PropHas e pp
  | PropParen pa -- preserve parens to rewrite infix apps after parsing
  -- Extra, primarily for the dictionary translation:
--  | PropLambda i pa
--  | PropLet i (Maybe t) e pa
  deriving (Eq,Show)

type PredArg e pp = Either e pp

-- Predicate formulas:
data PP i e p t pa pp
--  = PredId i -- just a special case of PredApp
  = PredApp i [t] [PredArg e pp] -- type arguments are added by the type checker
  | PredArrow pp pp
  | PredInfixApp pp i pp
  | PredNeg (Maybe t) pp
  | PredOp PropOp (Maybe t) pp pp
  | PredLfp i (Maybe t) pp
  | PredGfp i (Maybe t) pp
  | PredNil
  | PredLifted e
  | PredStrong pp
  | PredComp [(p,Maybe t)] pa
  | PredParen pp -- preserve parens to rewrite infix apps after parsing
  deriving (Eq,Show)



--- Source locations -----------------------------------------------------------

instance HasSrcLoc (PD i e t) where
   srcLoc (HsAssertion s _ _)   = s
   srcLoc (HsPropDecl  s _ _ _) = s
