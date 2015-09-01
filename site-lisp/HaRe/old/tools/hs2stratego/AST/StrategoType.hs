module StrategoType where
import Parentheses

data Type
  = TVar (P String)
  | TConst (P String)
  | TTuple (P [Type])
  | TInst (String,[Type])
  | TArrow (Type, Type)
  | TApp (Type, Type)
  deriving (Show{-,Read-})

data DataDecl
  = DCons (String,[(Strictness,Type)])
  deriving (Show{-,Read-})

data Strictness = Lazy | Strict
  deriving (Show{-,Read-})

tVar = TVar . P
tConst = TConst . P
tTuple = TTuple . P

tApp = curry TApp
tInst = curry TInst

tarrow = curry TArrow
tarrows ts t = foldr tarrow t ts

dCons = curry DCons
