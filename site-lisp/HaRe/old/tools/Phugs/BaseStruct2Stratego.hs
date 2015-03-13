{-+
Reusable functions for translation from the (non-recursive) base structure
to Stratego.
-}

module BaseStruct2Stratego where
import StrategoAST
import BaseSyntax hiding (EntSpec(..)) -- non-recursive base syntax structure
import PrettyPrint(pp)

transP trId trP p =
 case mapPI trId trP p of
   HsPId n -> Pvar (getHSName n) -- constructor vs variable ??
   HsPLit (HsInt _ i) -> Pconst i
   HsPInfixApp x op y -> Pcondata (getHSName op) [x,y] -- con vs var ??
   HsPApp n ps -> Pcondata n ps
   HsPTuple ps -> Ptuple ps
   HsPIrrPat p -> Ptilde p
   HsPParen p -> p
   _ -> error ("no "++pp p++" patterns yet")


transD trId trE trP trDs trT trC trTp d =
 case mapDI trId trE trP trDs trT trC trTp d of
   HsPatBind loc p b ds -> Val p (transRhs b) ds
   HsFunBind loc matches -> Fun (name matches) (map g matches)
      where name (HsMatch loc nm ps rhs ds: ms) =  nm
            g (HsMatch loc nm ps rhs ds) = (ps,transRhs rhs,ds)
   other -> error ("illegal dec "++pp d)
      
--transRhs :: HsRhs E -> B
transRhs (HsBody e) = Normal e
transRhs (HsGuard triples) = Guarded(map f triples)
        where f (loc,guard,body) = (guard,body)

--transAlt :: HsAlt E P [D] -> (P,B,[D])
transAlt (HsAlt loc pat rhs ds) = (pat,transRhs rhs,ds)


transE trId trE trP trDs trT trC e =
 case mapEI trId trE trP trDs trT trC e of 
   HsId n                 -> Var (getHSName n) -- constructor vs variable ??
   HsApp x y              -> App x y
   HsLit (HsInt _ i)      -> Const i
   HsInfixApp x op z      -> App (App (Var (getHSName op)) x) z -- con vs var ??
   HsNegApp _ x           -> App (Var "negate") x  
   HsLambda ps e          -> Abs ps e
   HsLet ds e             -> Let ds e
   HsIf x y z             -> Cond x y z
   HsCase e alts          -> Case e (map transAlt alts)
   HsTuple xs             -> TupleExp xs
   HsList xs              -> foldr cons nil xs
      where cons x xs = ConApp ":" [(x,Lazy),(xs,Lazy)]
	    nil = ConApp "[]" []
   HsParen x              -> x
   HsLeftSection x op     -> Abs[Pvar "zzz"] (App (App (Var (getHSName op)) x) 
                                             (Var "zzz"))
   HsRightSection op y    -> Abs[Pvar "zzz"] (App (App (Var (getHSName op)) 
                                             (Var "zzz")) y)
   other -> error ("no translation yet for: "++pp e)


--showId (HsVar x) = show x
--showId (HsCon x) = show x

showId x = pp x
