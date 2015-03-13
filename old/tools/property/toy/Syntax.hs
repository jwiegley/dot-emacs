-- $Id: Syntax.hs,v 1.1 2001/03/19 17:55:45 moran Exp $

module Syntax where


type Name = String


data Id
    = Var Name
    | Escape Name
      deriving (Eq, Show)

data E e v
    = App e e
    | Lambda [v] e
      deriving (Eq, Show)

data P id term prop
    = prop `And` prop
    | prop `Or` prop
    | prop `Implies` prop
    | prop `Iff` prop
    | term `Equiv` term
    | Exists id prop
    | All id prop
    | Truth
    | Falsehood
      deriving (Eq, Show)

-- Tie the knots

data Exp
    = ExpEval (E Exp Name)
    | ExpId Id
      deriving (Eq, Show)

data EscExp
    = EscExpEval (E EscExp Name)
    | EscExpId Id
      deriving (Eq, Show)

data Code e
    = Code e
      deriving (Eq, Show)

data Prop
    = Eval (E Prop Name)
    | Prop (P Id Exp Prop)
    | Term Exp
      deriving (Eq, Show)

data EscProp
    = EscEval (E EscProp Name)
    | EscProp (P Id (Code EscExp) EscProp)
    | EscTerm (Code EscExp)
      deriving (Eq, Show)
