module StrategoDecl where
import StrategoTerm(Def)
import StrategoProp(PredDecl,PropDecl)
import Parentheses

-- For top level declarations:

data Decl
  = Def (P Def)
  | Property (P PredDecl)
  | Assert (P PropDecl)
  | Ignored (P String)
  deriving (Show{-,Read-})

def = Def . P
property = Property . P
assert = Assert . P
ignored = Ignored . P
