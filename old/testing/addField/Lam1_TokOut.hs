module Lam1 where

data Expr = Var Int Int Int |
            Add Expr Expr


f = (\(Var var_1 x y) -> x + y)