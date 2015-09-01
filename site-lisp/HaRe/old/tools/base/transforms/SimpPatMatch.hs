module SimpPatMatch(module SimpPatMatch,HasOrig,HasIdTy,HasSrcLoc,ValueId) where
import Data.Maybe(isJust,fromMaybe)
import Substitute
import Recursive
import HasBaseStruct
import BaseSyntax hiding (Var)
import DefinedNames(definedVars)
import TiNames(ValueId,localVal')
--import TiPrelude(prelError,prelEqual,prelGE,prelMinus)
import TiClasses(HasDef,noDef,nullDef)
import TypedIds
import UniqueNames(orig,HasOrig)
import FreeNames
--import DefinedNames
import PrettyPrint(pp)
import MUtils(( # ),( <# ),apFst)

simpAllPatMatch ids m = mapExp (simpPatMatch ids) m

data SimpPatIds i = Ids {prelError,prelEqual,prelGE,prelMinus::HsIdentI i}
getSimpPatIds pv = Ids # pv "error" <# pv "==" <# pv ">=" <# pv "-"

class SimpPatMatch i s | s->i where
  simpPatMatch :: SimpPatIds i -> s -> s

instance SimpPatMatch i s => SimpPatMatch i [s] where
  simpPatMatch = map . simpPatMatch

simpPatMatchE ids e = simpPatMatchE' ids r e

simpPatMatchE' ids r e0 =
    case mapEI id (simpPatMatch ids) id (simpAllPatMatch ids) id id e0 of
      HsCase e alts -> convMatch ids (compilePatMatch ids e alts)
      e -> r e

{-+
Pattern match simplification, as described in section 3.17.3
of the Haskell 98 report.
-}
{-
compilePatMatch ::
   (ValueId i,HasSrcLoc i,HasIdTy n i,HasOrig i,HasOrig n,
    HasBaseStruct e (EI i e p ds t c),GetBaseStruct e (EI i e p ds t c),
    FreeNames i e,--DefinedNames i p,
    HasBaseStruct p (PI i p),GetBaseStruct p (PI i p),
    HasBaseStruct d (DI i e p ds t c tp),
    HasDef ds d)
  => SimpPatIds i -> e -> [HsAlt e p ds] -> Match i e p
--}
compilePatMatch ids = patMatch_a
  where
    Ids prelError prelEqual prelGE prelMinus = ids

    -- Rule (a)
    patMatch_a e alts =
        mustBeVar' "v0" (srcLoc alts) (Match e) (patMatch_b alts)

    -- Rule (b)
    patMatch_b alts v = foldr (patMatch_c v) err alts
      where
	err = nomatch s "No match"
	s = srcLoc alts

    nomatch s msg = NoMatch s msg

    -- Rule (c)
    patMatch_c v (HsAlt s p rhs ds) e' =
	case rhs of
	  HsBody e -> patMatch_c' v s p e ds e'
	  HsGuard gdrhss -> mustBeVar s e' rhs
	    where
	      rhs y = patMatch_c' v s p (ifGuards (hsEVar y) gdrhss) ds (Var y)
	      ifGuards = foldr ifGuard
	      ifGuard (s,g,e) = hsIf g e
      where
	-- Rule (c), after the guards have been handled
	patMatch_c' v s p e ds e' =
            patMatch_defghij v s p (hsLet' ds e) e'

    -- Introduce a variable to avoid code duplication, if necessary:
    mustBeVarM s e cont = mustBeVar s e (cont. Var)
    --mustBeVarE s e cont = mustBeVar s e (cont. hsEVar)
    mustBeVar s = mustBeVar' "y0" s
    mustBeVar' n s e cont =
      case isHsIdVar =<< basestruct =<< isMatch e of
	Just y -> cont y
	_ -> monoLet y e (cont y)
	  where
	    y = localVal' n (Just s)

    -- Rule (d)-(j)
    patMatch_defghij v s p rhs e' =
      case basestruct p of
	Just bp ->
	  case bp of
	    HsPIrrPat p' -> patMatch_d v s p' rhs -- rule (d)
	    HsPAsPat x p' -> patMatch_defghij v s p' (monoLetVar x v rhs) e' -- rule (e)
	    HsPWildCard -> rhs -- rule (f)
	    HsPApp k ps@(_:_) -> patMatch_g (srcLoc k) v (hsPApp k) ps rhs e' -- rule (g)
	    HsPTuple s ps -> patMatch_g s v (hsPTuple s) ps rhs e' -- rule (g)
	    HsPInfixApp p1 k p2 -> patMatch_g (srcLoc k) v k' [p1,p2] rhs e' -- rule (g)
	      where k' [p1,p2] = hsPInfixApp p1 k p2
	    HsPLit s lit -> -- rule (h) 
			  If (hsEVar v `eqTest` hsLit s lit) rhs e'
	    HsPNeg s lit ->
		If (hsEVar v `eqTest` hsNegApp s (hsLit s lit)) rhs e'
	    HsPSucc s n k -> -- rule (s), horror!!
		If (ve `geTest` ke) (monoLet n (Match (ve `minus` ke)) rhs) e'
	      where ve = hsEVar v ; ke = hsLit s k
	    HsPId (HsVar x) -> monoLetVar x v rhs -- rules (i) and (j)
	    HsPParen p' -> patMatch_defghij v s p' rhs e'
	    HsPList s ps -> patMatch_g s v (hsPList s) ps rhs e' -- rule (g), hmm!!
	    HsPRec k lps -> patMatch_mno v k lps rhs e'

	    _ -> keep
	_ -> keep
      where
	keep = patMatch_keep v s p rhs e'

	eqTest = binop prelEqual
	geTest = binop prelGE
	minus  = binop prelMinus

	binop op e1 e2 = hsId op `hsApp` e1 `hsApp` e2

    -- Rule (d)
    patMatch_d v s p' rhs =
	 monoLets xs (map proj xs) rhs
      where
	xs = map getHSName (definedVars p')
	proj x = patMatch_defghij v s p' (Match (hsEVar x))
					 (nomatch s "Irrefutable pattern failed")

    -- Rule (g)
    patMatch_g s v k ps rhs e' = mustBeVarM s e' (patMatch_g' s v k ps rhs)
    patMatch_g' s v k ps rhs e' =
	simpleCase v s p' body e'
      where
	 p' = k (map hsPVar xs)
	 xs = zipWith reuse ps (freshnames s 'x' ps)
	 body = foldr submatch rhs (zip xs ps)
	 submatch (x,p) rest = patMatch_defghij x s p rest e'

	 reuse p x = fromMaybe x (isPVar p)

    -- Rules (m)-(o), labelled fields
    patMatch_mno v k lps rhs e' =
      case lps of
	[] -> patMatch_o v k rhs e'
	[HsField f p] -> patMatch_n v k f p rhs e'
	HsField f p:lps' -> -- rule (m)
	   mustBeVarM (srcLoc k) e' $ \ ey ->
	   patMatch_n v k f p (patMatch_mno v k lps' rhs ey) ey

    -- Rule (n)
    patMatch_n v k f p rhs e' = simpleCase v (srcLoc k) p' rhs e'
      where p' = hsPApp k (map posPat fs)
	    posPat f' = if orig f'==orig f then p else hsPWildCard
	    fs = confields k

    -- Rule (o)
    patMatch_o v k rhs e' = simpleCase v (srcLoc k) p' rhs e'
      where p' = hsPApp k (replicate n hsPWildCard)
	    n = conarity k

patMatch_keep v = simpleCase v -- remaining cases and unimplemented rules

isMatch (Match e) = Just e
isMatch _ = Nothing

{-+
A data types to represent the output from the pattern match simplififier.
This makes further transformation easier.
-}
data Match i e p
  = NoMatch SrcLoc String
  | Match e
  | Var i -- special case for Match (hsEVar x)
  | MonoLets [i] [Match i e p] (Match i e p)
  | SimpleCase SrcLoc i p (Match i e p) (Match i e p)
  | If e (Match i e p) (Match i e p)

convMatch ::
  (HasBaseStruct p (PI i p),GetBaseStruct p (PI i p),HasDef ds d,HasIdTy n i,
   FreeNames i e,HasBaseStruct e (EI i e p ds t c))
  => SimpPatIds i -> Match i e p -> e
convMatch ids = conv . simp
  where
    Ids prelError prelEqual prelGE prelMinus = ids

    conv m =
      case m of
	NoMatch s msg -> nomatch s msg
	Match rhs -> rhs
	Var x -> hsEVar x
	MonoLets xs es m' -> monoLets xs (map conv es) (conv m')
	SimpleCase s v p rhs def -> simpleCase v s p rhs (flatten v def)
	If e m1 m2 -> hsIf e (conv m1) (conv m2)

    nomatch s msg = hsId prelError `hsApp` hsLit s (HsString (pp s++": "++msg))

    monoLets [] [] e' = e'
    monoLets xs0 es0 e' =
        hsParen (hsLambda' [hsPVar x|x<-xs] e') `apps` es
      where
	apps e es = foldl hsApp e es
	-- Omit bindings for variables that aren't used:
	(xs,es) = unzip . filter (keep.fst) $ zip xs0 es0
	keep x = x `elem` fvs_e'
	fvs_e' = fvs e'

    flatten v (SimpleCase s v' p rhs def) | v'==v =
        apFst ((s,p,rhs):) (flatten v def)
    flatten v m = ([],m)

    simpleCase v s p rhs ([],NoMatch{}) | irrefutable p =
	hsCase (hsEVar v) [alt (s,p,rhs)]
    simpleCase v s p rhs (alts,def) =
	hsCase (hsEVar v) (map alt ((s,p,rhs):alts)++default_alt)
      where
	default_alt = [alt (s,hsPWildCard,def)]

    alt (s,p,rhs) = HsAlt s p (HsBody (conv rhs)) noDef

    simp m =
      case m of
	MonoLets xs es m' -> case simpLet xs (map simp es) (simp m') of
                               ([], [] ,m') -> m'
			       (xs',es',m') -> MonoLets xs' es' m'
	SimpleCase s v p rhs def -> SimpleCase s v p (simp rhs) def'
          where def' = if irrefutable p
		       then NoMatch s "unreachable"
		       else simp def
	If e m1 m2 -> If e (simp m1) (simp m2)
	_ -> m

    simpLet xs es m = foldr simp1 ([],[],m) (zip xs es)
      where
        simp1 (x,e) (xs,es,m) =
	  case count x m of
	    0 -> (xs,es,m)
	    --1 -> (xs,es,subst e x m) -- causes code explosion in hs2alfa
	    _ -> (x:xs,e:es,m)

    -- Does x occur zero, one or many times in m?
    count x m =
      case m of
	NoMatch s msg -> 0
	Match rhs -> if x `elem` fvs rhs then 2 else 0::Int
	Var y -> if y==x then 1 else 0
	MonoLets xs es m' -> sum (map (count x) es)+count x m' -- x not in xs
	SimpleCase s v p rhs def ->
	    if v==x then 2 else count x rhs+count x def
	If e m1 m2 -> if x `elem` fvs e then 2 else count x m1+count x m2
{-
    -- pre: x occurs as Var x in one place
    subst e x m =
	case m of
	  NoMatch s msg -> m
	  Match rhs -> m
	  Var y -> if y==x then e else m
	  MonoLets xs es m' -> MonoLets xs (map su es) (su m')
	  SimpleCase s v p rhs def -> SimpleCase s v p (su rhs) (su def)
	  If e m1 m2 -> If e (su m1) (su m2)
      where su = subst e x
-}
    fvs e = [v|(HsVar v,ValueNames)<-freeNames e]

hsLambda' [] e = e
hsLambda' xs e = hsLambda xs e

simpleCase v s p rhs e' = SimpleCase s v p rhs e'

monoLetVar x y = if x==y then id else monoLet x (Match (hsEVar y))

-- Monomorphic, nonrecursive variants of let x = e in e'
-- (The Haskell report uses two versions)
--monoLet s x e e' = hsCase e [HsAlt s (hsPVar x) (HsBody e') noDef]
monoLet x e = MonoLets [x] [e]
monoLets [] [] e' = e'
monoLets xs es e' = MonoLets xs es e'

hsLet' ds e = Match (if nullDef ds then e else hsLet ds e)

irrefutable p =
  isJust (isPVar p) || isJust (isIrrPat p) || isWildCardPat p ||
  case isAsPat p of
    Just (_,p) -> irrefutable p
    _ -> False
  ||
  case basestruct p of
    Just (HsPTuple _ ps) -> all irrefutable ps
    Just (HsPInfixApp p1 k p2) -> concount k==1 && all irrefutable [p1,p2]
    Just (HsPApp k ps) -> concount k==1 && all irrefutable ps
    _ -> False

conarity k= conArity . conInfo $ k
confields k = conFields' . conInfo $ k

conFields' = fromMaybe [] . conFields

conInfo k = head [con|con<-constrs k,orig (conName con)==orig k]

concount k = length (constrs k)

constrs k =
  case idTy k of
    ConstrOf _ ti -> constructors ti

freshnames s x ps = [localVal' (x:show n) (Just s)|n<-[1..length ps]]
