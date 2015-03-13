module AST where

type Name = String

data Op = Plus | Mult | IntEq | IntLess

data LS = Lazy | Strict deriving Eq

data E
  = Var Name
  | App E E
  | Abs [P] E
  | Let [D] E
  | Case E [(P,B,[D])]
  | TupleExp [E]
  | Const Integer
  | ConApp Name [(E,LS)]
  | NewApp Name E
  | Boom
  | Undefined
--- Above is the "core", below various extras
  | Bin Op E E
  | Cond E E E
  | Tconst 
  | Fconst

-- Declarations
data D = Fun Name [([P],B,[D])] | Val P B [D]

-- Bodies
data B = Guarded [(E,E)] | Normal E

--- Nested Patterns
data P = Pconst Integer
       | Pvar Name
       | Ptuple [P]
       | Pcondata Name [P]  
       | Pnewdata Name P
       | Ptilde P



showB :: B -> String
showB (Normal e) = showE e
showB (Guarded ps) = foldr f "\n" ps
   where f (e1,e2) ans = "| "++(showE e1) ++ " = " ++(showE e2)++ ans

showD :: D -> String
showD (Val p body ds) =  " " ++ showP p ++ "=" ++ (showB body) ++ "\n" ++
                         "   where " ++ (showDs ds)
showD (Fun nm xs) = foldr (++) "" (map f xs)
   where f (ps,body,ds) = 
           nm ++ " " ++(showPs ps) ++ " = " ++(showB body) ++ "\n" ++
           "   where " ++ (showDs ds)
   

showDs dcls = foldr (++) "" (map showD dcls)


showOp :: Op -> String
showOp Plus = "+"
showOp Mult = "*"
showOp IntEq = "=="
showOp IntLess = "<"

showP (Pconst i) = show i
showP (Pvar n) = n
showP (Pcondata n ns) = 
                "(" ++ n ++ " " ++ 
                (foldr (\ s t -> if t/="" then (showP s) ++ "," ++ t
                                     else (showP s)) 
                        "" ns)
                ++ ")"
showP (Pnewdata n x) = "(" ++ n ++ " " ++ (showP x) ++ ")"              
showP (Ptilde p) = "~" ++ (showP p)

showPs [] = ""
showPs (p:ps) = (showP p)++" "++(showPs ps)

showE :: E -> String
showE (Const i) = show i
showE Tconst = "True"
showE Fconst = "False"
showE (Var nm) = nm
showE (Abs p d) = "(\\" ++ (foldr (++) " " (map showP p)) ++ " -> " ++ showE d ++ ")"
showE (App d d') = "(" ++ showE d ++ " " ++ showE d' ++ ")"
showE (Let dcls d) = "let " ++ 
                          foldr (++) "" (map showD dcls)
                            ++ 
                        " in " ++ showE d
showE (ConApp n l) =  "(" ++ n ++ " " ++  
                (foldr (\ (s,ls) t -> 
                            let sa = if (ls == Strict) then "!" else "" 
                            in
                                 if t/="" then sa ++ (showE s) ++ "," ++ t
                                     else sa ++ (showE s)) 
                        "" l)
                      ++ ")"
showE (NewApp n x) = "(" ++ n ++ " " ++  (showE x) ++ ")"                     
showE (Bin op d d') = "(" ++ showE d ++ " " ++ showOp op ++ " " ++ 
                               showE d' ++ ")"
showE Tconst = "true"
showE Fconst = "false"
showE (Case e ms) =
      "(case " ++ showE e ++ " of " ++ 
           (foldr (++) "" (map (\ alt -> "[" ++ (showAlt alt) ++ "]") ms)) ++ ")"
   where showAlt (p,b,ds) = show p ++ " -> " ++ show b ++ "\n" ++ showDs ds


instance Show E where
  show = showE

instance Show P where
  show = showP

instance Show B where
  show = showB
