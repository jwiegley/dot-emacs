module Lam1 where

data Expr = Var Int |
            Add Expr Expr


errorData field dat function
    =   errorExpr
            ("the binding for " ++ field ++ " in a pattern binding involving " ++ dat ++ " has been removed in function " ++ function)

f = (\(Var  y) -> errorExpr "x" "Var" "f" + y)