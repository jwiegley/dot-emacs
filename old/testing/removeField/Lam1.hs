module Lam1 where

data Expr = Var Int Int |
            Add Expr Expr


f = (\(Var x y) -> x + y)