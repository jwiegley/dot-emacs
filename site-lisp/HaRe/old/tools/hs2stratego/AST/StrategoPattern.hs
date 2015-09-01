module StrategoPattern where
import Parentheses

data Literal
  = HInt (P Integer)
  | HChar (P String) -- character literals in Stratego?
  | HString (P String) -- desugar into list of characters?
  | HFrac (P Rational)
  deriving (Show{-,Read-})

hInt = HInt. P
hChar = HChar . P
hString = HString . P
hFrac = HFrac . P

data Pattern
  = NoPattern
  | NewPattern (P String)
  | WildCard
  | VarPat (P String)
  | ConstrPat (String, [Pattern])
  | AsPattern (String, Pattern)
  | TuplePat (P [Pattern])
  | LitPat (P Literal) -- new
{- old
  | LitPat (P Integer)
  | CharLitPat (P Char)
  | StringLitPat (P String)
-}
  | TwiddlePat (P Pattern)

  | FunPat (String, [Pattern])
  deriving (Show{-,Read-})

varPat = VarPat . P
tuplePat = TuplePat . P
litPat = LitPat . P
--charLitPat = CharLitPat . P
--stringLitPat = StringLitPat . P
twiddlePat = TwiddlePat . P

pcons x xs = ConstrPat (":", [x,xs])
pnil = ConstrPat ("[]", [])
plist = foldr pcons pnil
