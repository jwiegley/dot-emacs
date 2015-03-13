module List1 where
data Expr
    = Var String Int Int | Add Expr Expr | Mul Expr Expr
 
eval :: [Expr] -> [Int]
 
eval xs = [x | (Var x y) <- xs]
 