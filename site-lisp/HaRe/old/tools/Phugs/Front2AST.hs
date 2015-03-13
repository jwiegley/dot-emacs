module Front2AST where

import Syntax
import PrettyPrint(pp)

type Name = String
data Op = Plus | Mult | IntEq | IntLess
data LS = Lazy | Strict deriving Eq

data Pat 
  = Pconst Integer         -- { 5 }
  | Pvar Name              -- { x }
  | Ptuple [Pat]           -- { (p1,p2) }
  | Pcondata Name [Pat]    -- data T1 = C1 t1 t2 \nl {C1 p1 p1} = e 
  | Pnewdata Name Pat      -- newtype T2 = C2 t1 t2 \nl {C2 p1 p2} = e
  | Ptilde Pat             -- { ~p }
data Exp 
  = Var Name               -- { x }
  | Const Integer          -- { 5 }
  | App Exp Exp            -- { f x }
  | Abs [Pat] Exp          -- { \ p1 p2 -> e }
  | TupleExp [Exp]         -- { (e1,e2) }
  | ConApp Name [(Exp,LS)] -- data T1 = C1 t1 t2 \nl p = {C1 e1 e2}
  | NewApp Name Exp        -- newtype T2 = C2 t1 t2 \nl p = {C2 e1 e2}
  | Seq Exp Exp            -- { seq e1 e2 }               
  | Bin Op Exp Exp         -- { e1 + e2 }
  | Cond Exp Exp Exp       -- { if e1 then e2 else e3 }
  | Let [Dec] Exp          -- { let x=e1 \nl   y=e2 in e3 }
  | Case Exp [Match]       -- { case e of m1 \nl m2 }
type Match = 
      (Pat, Body, [Dec])   -- case e of { pat -> body where decs } 
data Dec 
  = Fun Name [Clause]      -- { f p1 p2 = b where decs }
  | Val Pat Body [Dec]     -- { p = b where decs }
type Clause = 
      ([Pat],Body,[Dec])   -- f { p1 p2 = body where decs }
data Body
  = Guarded [(Exp,Exp)]    -- f p { | e1 = e2 | e3 = e4 } where ds
  | Normal Exp             -- f p = { e } where ds


showB :: Body -> String
showB (Normal e) = showE e
showB (Guarded ps) = foldr f "\n" ps
   where f (e1,e2) ans = "| "++(showE e1) ++ " = " ++(showE e2)++ ans

showWhere ds = if null ds then "" else "   where "

showD :: Dec -> String
showD (Val p body ds) =  "VALDEF " ++ showP p ++ "=" ++ (showB body) ++ "\n" ++
                         (showWhere ds) ++ (showDs ds)
showD (Fun nm xs) = "FUNDEF "++ foldr (++) "" (map f xs)
   where f (ps,body,ds) = 
           nm ++ " " ++(showPs ps) ++ " = " ++(showB body) ++ "\n" ++
           (showWhere ds) ++ (showDs ds)
   

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

showE :: Exp -> String
showE (Var nm) = nm
showE (Const i) = show i
showE (App d d') = "(" ++ showE d ++ " " ++ showE d' ++ ")"
showE (Abs p d) = "(\\" ++ (foldr (++) " " (map showP p)) ++ " -> " 
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
showE (NewApp n x) = "(" ++ n ++ " " ++  (showE x) ++ ")"                     
showE (Seq x y) = "(seq "++(showE x) ++ " " ++ (showE y) ++ ")"
showE (Bin op d d') = "(" ++ showE d ++ " " ++ showOp op ++ " " ++ 
                               showE d' ++ ")"
showE (Cond b e1 e2) = "if "++showE b++" then "++showE e1++" else "++show e2
showE (Let dcls d) = "let " ++ 
                          foldr (++) "" (map showD dcls)
                            ++ 
                        " in " ++ showE d
showE (Case e ms) =
      "(case " ++ showE e ++ " of " ++ 
           (foldr (++) "" 
           (map (\ alt -> "[" ++ (showAlt alt) ++ "]") ms)) ++ ")"
   where showAlt (p,b,ds) = show p ++ " -> " ++ show b ++ "\n" ++ showDs ds


instance Show Dec where
  show = showD

instance Show Exp where
  show = showE

instance Show Pat where
  show = showP

instance Show Body where
  show = showB

-----------------------------------------------------------------------

bad x = error "not yet"

--trP :: HsPat -> Pat
trP (Pat p) =
 case mapP trP p of
   HsPId n -> Pvar (showId n)
   HsPLit (HsInt _ n) -> Pconst n
   HsPInfixApp x op y -> Pcondata (showId op) [x,y]
   HsPApp n ps -> Pcondata (showId n) ps
   HsPTuple ps -> Ptuple ps
   HsPIrrPat p -> Ptilde p
   HsPParen p -> p
   other -> error ("no "++(show other)++" patterns yet")


--trD :: HsDecl -> Dec
trD (d @ (Dec x)) =
 case mapD trE trP (map trD) bad bad bad x of
   HsPatBind loc p b ds -> Val p (trRhs b) ds
   HsFunBind loc matches -> Fun (name matches) (map g matches)
      where name ((HsMatch loc nm ps rhs ds): ms) = (showId (HsVar nm))
            g (HsMatch loc nm ps rhs ds) = (ps,trRhs rhs,ds)
   other -> error ("illegal dec "++(pp d))          
      
--trRhs :: HsRhs Exp -> Body
trRhs (HsBody e) = Normal e
trRhs (HsGuard triples) = Guarded(map f triples)
        where f (loc,guard,body) = (guard,body)

--trAlt :: HsAlt Exp Pat [Dec] -> (Pat,Body,[Dec])
trAlt (HsAlt loc pat rhs ds) = (pat,trRhs rhs,ds)

--trE :: HsExp -> Exp
trE (e @ (Exp x)) = 
 case mapE trE trP (map trD) bad bad x of 
   HsId n                 -> Var (showId n)
   HsApp x y              -> App x y
   HsLit (HsInt _ n)      -> Const n
   HsInfixApp x op z      -> App (App (Var (showId op)) x) z
   HsNegApp _ x           -> App (Var "negate") x  
   HsLambda ps e          -> Abs ps e
   HsLet ds e             -> Let ds e
   HsIf x y z             -> Cond x y z
   HsCase e alts          -> Case e (map trAlt alts)
   HsTuple xs             -> TupleExp xs
   HsList xs              -> f xs
      where f [] = ConApp "[]" []
            f (x:xs) = ConApp ":" [(x,Lazy),(f xs,Lazy)]
   HsParen x              -> x
   HsLeftSection x op     -> Abs[Pvar "zzz"] (App (App (Var (showId op)) x) 
                                             (Var "zzz"))
   HsRightSection op y    -> Abs[Pvar "zzz"] (App (App (Var (showId op)) 
                                             (Var "zzz")) y)
   other -> error ("no translation yet for: "++(pp e))


--showId (HsVar x) = show x
--showId (HsCon x) = show x

showId x = pp x
