module Prop2Alfa(Prop2Alfa.transModule,modPath) where
import TiPropDecorate
import PropSyntax(HsModuleI,HsPatI,prop,Prop,Rec(..))
import qualified PropSyntax as PS
import HsConstants(mod_Prelude)
import PNT
import TypedIds
import HsPropStruct
import HsPropMaps
import HsIdent
import QualNames(mkUnqual,getQualified)
import UniqueNames(noSrcLoc,origModule)
import DefinedNames(definedType)
import PrettyPrint(Printable,pp)
import TI hiding (getEnv,inst,tapp,sch,inEnv,extend,restrict,conName,definedType)
import NameMapsPropDecorate
import BaseStruct2Alfa
import qualified UAbstract as U
import qualified AbstractOps as U
import qualified UMatch as U
import MUtils
import EnvM
import Maybe(fromMaybe)
import Char(isAlpha)

transModule = trans :: HsModuleI m i (TiDecls NName) -> EnvM Env U.Module

instance (Trans b u,Trans p u) => Trans (Prop b p) u where
  transTyped t p = prop tt tt p
    where tt x = transTyped t x

instance Trans (TiAssertion NName) U.Exp where transTyped = transTypedRec
instance Trans (TiPredicate NName) U.Exp where transTyped = transTypedRec

instance Trans (OTiAssertion NName) U.Exp where
  trans (OA is ds pa) = 
      --U.uAbsExp
      U.piExp . map (flip (,) (missing "assertion dictionary type"))
        # ltrans is <# (eLet # mapM transT ds <# trans pa)
    where
      transT (i:>:t,e) =
	do i' <- transUnqualVar i
	   t' <- trans t
	   e' <- trans e
	   return $ U.decl' [valdef i' ([],([],t')) e']
			  
instance (Printable pa,Printable pp,
	  Trans pa U.Exp,Trans pp U.Exp)
       => Trans (PD NName pa pp) [U.Def] where
  trans pd =
      case pd of
        HsAssertion s optnm pa -> maybe cmnt (transAssert pa) optnm
        HsPropDecl s nm is pp -> transPropDecl nm  is pp
    where
      cmnt = return [commentdef pd]

      transAssert pa nm =
	do (gs,cs:=>t) <- schak (HsCon nm)
	   extendTyvars gs $ do
	     -- assume t=Prop
	     -- t' <- trans t -- should be Prop
	     gs' <- ltrans gs
	     cs' <- ltrans cs
	     nm' <- trans nm
	     pa' <- trans pa
	     let cnt=length gs
	     return $
               --hide' nm' cnt++
	       [valdef nm' ([],([],{-U.eFuns cs'-}eAssertion))
		           (U.piExp gs' (dictTypes cs' pa'))]

      dictTypes ts = uncurry U.piExp . apFst dictTypes' . U.flatPi
        where dictTypes' xts = zip (map fst xts) ts++drop (length ts) xts

      transPropDecl n is pp =
        do n' <- transUnqualVar n
           sch@(gs,cs:=>t) <- schk (HsCon n) -- or schak...
	   extendTyvars gs $ do
	     tctx <- ltrans gs
	     cs' <- ltrans cs
	     (targs,tres) <- U.flatFun # trans t
	     is' <- ltrans (map getHSName is)
	     let (ctx,tres') = args' is' (cs'++targs) tres
	         cnt=length gs
	     pp' <- trans pp
	     return $ hide' n' cnt++[valdef n' (tctx++ctx,tres') pp']

eProp = un "Prop"
eAssertion = un "Assertion"
--eProp = U.eType
ePred = uApp (un "Pred")

instance (Trans e U.Exp,Trans t U.Exp,Trans pa U.Exp,Trans pp U.Exp)
      => Trans (PA NName e t pa pp) U.Exp where
    trans pa =
      case pa of
	Quant All i optt pa -> do i' <- trans i
                                  optt' <- trans optt
				  U.EPi (i' U.:- opt "type in universal quantifier" optt') # trans pa
	Quant q i optt pa -> do i' <- trans i
				optt' <- trans optt
                                uApp # transQ q optt' <#
				     (eAbs i' optt' # trans pa)
			     
--	PropId i -> U.EVar # i
	PropApp i ts es -> appqvar # transConId i <# ltrans ts <# mapM (either trans trans) es
	PropNeg a -> uApp eNot # trans a
	PropOp op a1 a2 -> U.app # trans op <# ltrans [a1,a2]
	PropEqual e1 e2 -> equal # trans e1 <# trans e2
	PropHas e p -> uApp # trans p <# trans e
	PropParen a -> trans a

eAbs n optt e = U.EAbs (n U.:-opt "type in abstraction" optt) e
eNot = un "Not"
ePredNot = un "NegPred"
--eEq =  m1 (un "Identical")

m1 s e =uApp e (missing s)
m2 s = m1 s . m1 s

-- The type checker is assumed to add a type annotation to the left operand
equal (U.ETyped e1 t1) e2 = U.app (un "===") [t1,e1,e2]
equal e1 e2 = U.app (un "===") [missing "type in equality prop",e1,e2]

transQ q optt = flip uApp (opt "type in quantifier" optt) # trans q

instance Trans Quantifier U.Exp where
  trans q =
    return $
    case q of
      All   -> un "ForAll"
      Exist -> un "Exists"

instance Trans PropOp U.Exp where
  trans op =
    return $
    case op of
     Conj  -> un "And"
     Disj  -> un "Or"
     Imp   -> un "Implies"
     Equiv -> un "Equivalence"

appvar i ts es = U.app (U.EVar i) (ts++es)
appqvar e ts es = U.app e (ts++es)

instance (Trans c U.Exp,Trans t U.Exp) => Trans (PS.Q [c] t) U.Exp where
  trans (c PS.:=> t) = U.eFuns # ltrans c <# trans t

instance (Trans e U.Exp,Trans p U.Pat,Trans t U.Exp,
	  Trans pa U.Exp,Trans pp U.Exp,
	  Printable e,Printable p,Printable t,Printable pa,Printable pp)
      => Trans (PP NName e p t pa pp) U.Exp where
  trans p =
    case p of
--    PredId i -> U.EVar # trans i
      PredApp i ts ps -> appqvar # transConId i
                               <# ltrans ts <# mapM (either trans trans) ps
      PredArrow p1 p2 -> U.app (m2 "type for arrow predicate" (un "Arrow")) # ltrans [p1,p2]
      PredInfixApp p1 i p2 -> U.app . U.EVar # trans i <# ltrans [p1,p2]
      PredNeg optt p -> liftNeg # trans optt <# trans p
      PredOp op optt p1 p2 -> liftOp # trans op <# trans optt <# trans p1 <# trans p2
      PredLfp i optt p -> fix "Lfp" # trans i <# trans optt <# trans p
      PredGfp i optt p -> fix "Gfp" # trans i <# trans optt <# trans p
      PredNil -> return (m1 "type for IsNil" (un "IsNil"))
      PredLifted e -> uApp (m1 "type for !" (un "Lift")) # trans e
      PredStrong p -> trans p -- !!
      PredParen p -> trans p
      PredComp pts a -> foldr abstr # trans a <# ltrans pts
      _ -> return $ missing (comment (pp p)) -- for unimplemented things
    where
      abstr (U.PVar x,optt) e = eAbs x optt e
      abstr _ _ = missing "pattern in predicate comprehension" -- !!!

      liftNeg optt p =
          U.app ePredNot [opt "type of lifted negation" (deep # optt),p]

      liftOp op optt p1 p2 =
          U.app (un "predOp")
                [opt "type of lifted connective" (deep # optt),op,p1,p2]

      fix op i optt p = U.app (un op) [opt "type in Gfp/Lfp" optt,eAbs i (ePred # optt) p]

      deep t =
        case t of
	  U.EApp f t2 | f==un "predT" -> deep t2 -- compensation for shallow translation of t
	  U.EPi (x U.:-t1) t2 -> U.app predCon [t1,deep t2]
	  _ -> if t==propType
	       then propCon
	       else t -- must be a type variable of kind Prop
		
      predCon = U.ECon (U.Con "Pred")
      propCon = U.ECon (U.Con "Prop")
      propType = qn (transM mod_Prelude) "Prop"
----

instance Trans (TiDecls NName) [U.Def] where
  trans (Decs ds env) = concat # extend env (ltrans ds)

instance Trans (TiDecl NName) [U.Def] where
  trans (Dec d) = prop transBase trans d
    where transBase d = (++) # trans d <# liftedCons d

instance Trans (HsPatI NName) U.Pat where trans = trans . struct

instance Trans (TiExp NName) U.Exp where
  trans (Exp e) = trans e
  trans (TiSpec c@(HsCon _) sc ts) = transECon c sc ts
  --trans (TiSpec x _ []) = transEVar x
  trans s@(TiSpec x _ ts) = U.app # inst x <# ltrans ts
  trans (TiTyped e t) = transTyped (Just t) e

  transTyped t (Exp e) = transTyped t e
  transTyped t e = optTransTyped t =<< trans e

------

transRec = trans . struct
transTypedRec t = transTyped t . struct

------

liftedCons d =
  concat #
  case d of
    PS.HsNewTypeDecl s ctx lhs con  der -> liftedCons' lhs
    PS.HsDataDecl    s ctx lhs cons der -> liftedCons' lhs
    _ -> return []
  where
    liftedCons' = liftedCons'' . definedType

    liftedCons'' t@(PNT tn _ _) =
        mapM liftedCon [splitAt i cs'|i<-[0..length cs'-1]]
      where
        cs' = [(pnt (conName c) cty,conArity c)|c<-cs]
        Type tinfo@(TypeInfo {constructors=cs}) = idTy t
	cty = ConstrOf (getQualified tn) tinfo

    liftedCon (cs1,(c,n):cs2) =
	do (gs,qt) <- schk (HsCon c)
	   gs' <- ltrans gs
	   qt' <- extendTyvars gs (trans qt)
	   let ps = gs'++zip pns (map ePred args)++[(x0,res)]
	       (args,res)=U.flatFun qt'
	   c' <- transUnqualVar c
	   other <- mapFstM (\c -> trConName # trans c) (cs1++cs2)
	   let cpred = trPredName c'
	       ccon = trConName c'
	       body = predBody ccon n other
	   return $ hide cpred gs ++[valdef cpred (ps,([],eProp)) body]

       where
         pns = [U.Var ("P"++show i)|i<-[1..n]]
	 x0:xs =[U.Var ("x"++show i)|i<-[0..]]

         predBody c n other = U.ECase (U.EVar x0)
				      (rightBranch:map otherBranch other)
           where
	     rightBranch       = br c n (conj (zipWith varapp pns xs))
	     otherBranch (c,n) = br c n (un "Absurdity")

	     br (U.Var c) n e = U.Branch (U.Con c,(take n xs,e))
	     varapp p x = U.EVar p `uApp` U.EVar x

	     conj [] = un "Triviality"
	     conj ps = foldr1 (uApp . uApp (un "And")) ps

    pnt c idty = PNT (mkUnqual c) idty noSrcLoc

    trPredName (U.Var s) = U.Var . predName . transConName $ s
    trConName (U.Var s) = U.Var . transConName $ s

transConId i =
  if isCon i
  then qn' (transM (origModule i)) # getMEnv <# (liftedConName # trans i)
  else U.EVar # trans i

qn' m ms v@(U.Var x) = if m `elem` ms then U.EVar v else qn m x

liftedConName (U.Var s) = U.Var (predName s)

predName s =
  case s of
    c:_ | isAlpha c -> "Pred"++s
    _ -> "%"++s
