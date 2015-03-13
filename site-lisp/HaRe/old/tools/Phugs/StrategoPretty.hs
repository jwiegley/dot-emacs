module StrategoPretty where
import StrategoAST

showB :: B -> String
showB (Normal e) = showE e
showB (Guarded ps) = foldr f "\n" ps
   where f (e1,e2) ans = "| "++(showE e1) ++ " = " ++(showE e2)++ ans

showWhere ds = if null ds then "" else "   where "

showD :: D -> String
showD (Val p body ds) =  " " ++ showP p ++ "=" ++ (showB body) ++ "\n" ++
                         (showWhere ds) ++ (showDs ds)
showD (Fun nm xs) = foldr (++) "" (map f xs)
   where f (ps,body,ds) = 
           nm ++ " " ++(showPs ps) ++ " = " ++(showB body) ++ "\n" ++
           (showWhere ds) ++ (showDs ds)
   

showDs dcls = foldr (++) "" (map showD dcls)

showOp :: Op -> String
showOp Plus = "+"
showOp Mult = "*"
showOp IntEq = "=="
showOp IntLess = "<"

showP (Pconst i)      = "LitPat("++show i++")"
showP (Pvar n)        = "VarPat(\""++n++"\")"
showP (Pcondata n ns) = "ConstrPat(" ++ n ++ "," ++ (mkSlist ns) ++")"
showP (Paspat n p)    = "AsPattern("++n++","++show p++")"
showP (Pnewdata n x)  = error "no new constructor pattern yet"
showP (Ptilde p)      = error "no tilde pattern yet"
showP (Ptuple ps)     = "TuplePat(" ++ mkSlist ps ++ ")" 
showP Pwildcard       = "WildCard"

showPs [] = ""
showPs (p:ps) = (showP p)++" "++(showPs ps)

{- Pretty prints a haskell list expression into a stratego list -}
mkSlist = foldr 
             (\ s t -> if t/="Nil" then (show s++","++t) else (show s))
             "Nil" 

{- N.b., the resulting string is Stratego code -}
showE :: E -> String
showE (Var nm)     = "HVar(\""++nm++"\")"
showE (Const i)    = "HLit("++show i++")"
showE (App d d')   = "HApp(" ++ showE d ++ "," ++ showE d' ++ ")"
showE (Abs p d)    = "(\\" ++ (foldr (++) " " (map showP p)) ++ " -> " 
                           ++ showE d ++ ")"
showE (TupleExp l) =  "(" ++   
                (foldr (\ s t -> 
                            if t/="" then (showE s) ++ "," ++ t
                                     else (showE s)) 
                       "" l)
                      ++ ")"
showE (ConApp n l) =  "(" ++ n ++ " " ++  
                (foldr (\ (s,ls) t -> 
                            let sa = if (ls == Strict) then "!" else "" 
                            in
                                 if t/="" then sa ++ (showE s) ++ "," ++ t
                                     else sa ++ (showE s)) 
                        "" l)
                      ++ ")"
showE (NewApp n x)  = "(" ++ n ++ " " ++  (showE x) ++ ")"                     
showE (Seq x y)     = "(seq "++(showE x) ++ " " ++ (showE y) ++ ")"
showE (Bin op d d') = "(" ++ showE d ++ " " ++ showOp op ++ " " ++ 
                               showE d' ++ ")"
showE (Cond b e1 e2) = "if "++showE b++" then "++showE e1++" else "++show e2
showE (Let dcls d)   = "let " ++ 
                            foldr (++) "" (map showD dcls)
                              ++ " in " ++ showE d
showE (Case e ms) =
      "(case " ++ showE e ++ " of " ++ 
           (foldr (++) "" 
           (map (\ alt -> "[" ++ (showAlt alt) ++ "]") ms)) ++ ")"
   where showAlt (p,b,ds) = show p ++ " -> " ++ show b ++ "\n" ++ showDs ds


instance Show D where
  show = showD

instance Show E where
  show = showE

instance Show P where
  show = showP

instance Show B where
  show = showB
