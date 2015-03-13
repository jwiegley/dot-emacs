module List1 where

data Expr = Var Int |
            Add Expr Expr |
            Mul Expr Expr


errorData field dat function
    =   errorExpr
            ("the binding for " ++ field ++ " in a pattern binding involving " ++ dat ++ " has been removed in function " ++ function)

eval :: [Expr] -> [Int]
eval xs = [errorExpr "x" "Var" "eval" | (Var  y) <- xs]