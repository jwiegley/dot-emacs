module ToQC(moduleToQC) where

-- haskell syntax
import HsName
import HasBaseStruct
--import PrettyPrint(pp)
import HsExp(EI,mapEI,seqEI)
import HsPat(PI,isPVar)
import HsDecl(DI,HsMatchI(..),mapDI,seqDI)
import HsGuards(HsRhs(..))
import HsFields(HsFieldI(..))
import HsLiteral(HsLiteral(..))
import SrcLoc(loc0)

import WorkModule(inscpRel)
import Relations(applyRel)
--import Ents(Ent(..))
import TypedIds(IdTy(..),idTy)
import SourceNames(fakeSN)
import QualNames(getQualified)

-- property syntax
import PropSyntax as Prop hiding (quant)
import Syntax     as Hs


-- utils
import List(nub)
import Maybe(isJust,fromJust)
import MUtils (( # ))
import StateM



class Trans t e | t -> e where trans :: t -> e


-- names of combinators
qc = Qual (PlainModule "QC") 

neg     = qc "not"
conj    = qc "/\\"
disj    = qc "\\/"
impl    = qc "==>"
equiv   = qc "<==>"
false   = qc "false"
true    = qc "true"
forAll  = qc "forAll"
exists  = qc "exists"
arrow   = qc "-=>"
nil     = Qual mod_Prelude "nil"
lft     = qc "!"
lfp     = qc "lfp"
gfp     = qc "gfp"
equal   = qc "==="
formula_type  = qc "F"

pneg     = qc "pNot"
pconj    = qc "^/\\"
pdisj    = qc "^\\/"
pimpl    = qc "^==>"
pequiv   = qc "^<==>"


transOp Conj  = HsVar conj 
transOp Disj  = HsVar disj
transOp Imp   = HsVar impl
transOp Equiv = HsVar equiv

transPredOp Conj  = HsVar pconj 
transPredOp Disj  = HsVar pdisj
transPredOp Imp   = HsVar pimpl
transPredOp Equiv = HsVar pequiv


predName y  
  | isConOp y = mapHsName ("%" ++) y
  | isTuple y = mapHsName (\s ->"pred_Tuple"++show (tupleArity s)) y
  | otherwise = mapHsName ("pred_" ++) y
  where
    isTuple y = case hsUnQual y of
		 '(':_ -> True
		 _ -> False

    tupleArity "()" = 0
    tupleArity s = 1+length (filter (==',') s)

assertName  = mapHsName ("assert_" ++)


string (UnQual x) = hsLit loc0 (HsString x)
string _          = error "Qualified names not allowd in quantifiers."

f $$ x = hsApp f x

pInfixApp e1 op e2 = hsInfixApp (hsParen e1) op (hsParen e2)

class SplitType t' c t | t' -> t c where
  splitType :: t' -> (c,t)

instance SplitType (Q [c] t) [c] t where
  splitType (c :=> t) = (c,t)


instance (Trans pa e, Trans pp e, Trans e' e, SplitType t' [c] t,
          HasBaseStruct e (EI HsName e p [d] t [c]), 
          HasBaseStruct p (PI HsName p),
          HasBaseStruct t (TI HsName t))
  => Trans (PA HsName e' t' pa pp) e where
  trans (Quant All x t pa)      = quant forAll x t pa
  trans (Quant Exist x t pa)    = quant exists x t pa
--trans (PropId i)              = hsEVar (assertName i)
  trans (PropApp i ts es)       = foldl ($$) (hsEVar (predName i)) (map (either trans trans) es)
  trans (PropNeg pa)            = hsEVar neg $$ trans pa
  trans (PropOp op p1 p2)       = pInfixApp (trans p1) (transOp op) (trans p2)
  trans (PropEqual e1 e2)       = pInfixApp (trans e1) (HsVar equal) (trans e2)
  trans (PropHas e pp)          = hsParen (trans pp) $$ trans e
  trans (PropParen pa)          = hsParen (trans pa)


quant name x t pa               = hsEVar name $$ string x $$ body
  where exp                     = hsLambda [hsPVar x] (trans pa)
        body                    = case t of 
                                    Nothing -> exp
                                    Just t  -> hsExpTypeSig loc0 (hsParen exp) ctxt (hsTyFun ty (hsTyCon formula_type))
                                      where (ctxt,ty) = splitType t



instance (Trans pa e, Trans pp e, Trans e' e,
          HasBaseStruct e (EI HsName e p [d] t [c]),  
          HasBaseStruct p (PI HsName p),
          GetBaseStruct p (PI HsName p),
          HasBaseStruct d (DI HsName e p [d] t [c] tp))
  => Trans (PP HsName e' p t1 pa pp) e where
--trans (PredId i)              = hsEVar (predName i)
  trans (PredApp i ts xs)       = foldl ($$) p (map (either trans trans) xs)
    where p                     = hsEVar (predName i)
  trans (PredArrow p1 p2)       = pInfixApp (trans p1) (HsVar arrow) (trans p2)
  trans (PredInfixApp p1 i p2)  = pInfixApp (trans p1) p (trans p2) 
    where p                     = HsVar (predName i)
  trans (PredNeg oppt p)        = hsEVar pneg $$ trans p
  trans (PredOp op optt p1 p2)	= pInfixApp (trans p1) (transPredOp op) (trans p2)
  trans (PredLfp i _ pp)        = hsEVar lfp $$ hsLambda [hsPVar (predName i)] (trans pp)
  trans (PredGfp i _ pp)        = hsEVar gfp $$ hsLambda [hsPVar (predName i)] (trans pp)
  trans PredNil                 = hsEVar nil
  trans (PredLifted e)          = hsEVar lft $$ trans e
  trans (PredStrong pp)         = trans pp
  trans (PredComp ps pa) 
    | allVars                   = hsLambda pats exp 
    | otherwise                 = hsLet [hsFunBind loc0 ms] (hsEVar x)
    where allVars               = all isJust (map isPVar pats)
          (pats,tys)            = unzip ps
          exp                   = trans pa
          ms                    = [ HsMatch loc0 x pats (HsBody exp) []
                                  , HsMatch loc0 x (map und ps) (HsBody $ hsEVar false) []
                                  ]
          und _                 = hsPWildCard
          x                     = UnQual "it"
  trans (PredParen pp)          = hsParen (trans pp)  


instance (HasBaseStruct e (EI HsName e p [d] t [c]), Trans d' d, Trans e' e) => Trans (EI HsName e' p [d'] t [c]) e where
  trans = base . mapEI id trans id (map trans) id id

instance (HasBaseStruct d (DI HsName e p [d] t [c] tp), Trans d' d, Trans e' e) => Trans (DI HsName e' p [d'] t [c] tp) d where
  trans = base . mapDI id trans id (map trans) id id id


instance (Trans d' d, Trans e' e, Trans pa e, Trans pp e,
           HasBaseStruct d (DI HsName e p [d] t [c] tp),
           HasBaseStruct e (EI HsName e p [d] t [c]),
           GetBaseStruct e (EI HsName e p [d] t [c]),
           HasBaseStruct p (PI HsName p))
          => Trans (PropDI HsName e' p [d'] t [c] tp pa pp) d where
  trans = prop trans transPD


-- PRE: all assertions are named

transPD :: (Trans pa e, Trans pp e, 
            HasBaseStruct d (DI HsName e p [d] t [c] tp),
            HasBaseStruct e (EI HsName e p [d] t [c]),
            GetBaseStruct e (EI HsName e p [d] t [c]),
            HasBaseStruct p (PI HsName p))
        => PD HsName pa pp -> d
transPD (HsAssertion loc (Just i) pa) =
    hsPatBind loc (hsPVar (assertName i)) (HsBody (trans pa)) []
transPD (HsPropDecl loc i xs pp)      =
    case basestruct body of
      Just (HsLambda ps e) -> bind (map cvt xs ++ ps) e
      _    -> if null xs then bind [hsPVar x]
			           (hsParen body $$ hsEVar x)
                         else bind (map cvt xs) body

  where cvt (HsCon i)                 = hsPVar (predName i)
        cvt (HsVar i)                 = hsPVar i
        body                          = trans pp
        bind ps body                  = hsFunBind loc [HsMatch loc (predName i) ps (HsBody body) []]
        x                             = UnQual "x"

transPD (HsAssertion _ Nothing _)     = error "unnamed assertion?"





--- recursive -----------------------------------------------------------------
instance Trans (AssertionI HsName) (Hs.HsExpI HsName)     where trans = trans . struct
instance Trans (PredicateI HsName) (Hs.HsExpI HsName)     where trans = trans . struct
instance Trans (Prop.HsExpI HsName) (Hs.HsExpI HsName)    where trans = trans . struct
instance Trans (Prop.HsDeclI HsName) (Hs.HsDeclI HsName)  where trans = trans . struct




--------------------------------------------------------------------------------
-- generating predicates for lifted constructors
--------------------------------------------------------------------------------

gen' compNum pat loc name     = hsFunBind loc matches
  where matches               = [ HsMatch loc lftCon (predPats ++ [pat compNames]) (HsBody body) []
                                , HsMatch loc lftCon (predPats ++ [hsPWildCard])   (HsBody (hsEVar false)) []
                                ] 
        lftCon                = predName name
        body                  = foldr app (hsEVar true) (zipWith ($$) (map hsEVar predNames) (map hsEVar compNames))
          where app e1 e2     = pInfixApp e1 (HsVar conj) e2
        names x               = take compNum [ UnQual (x ++ show n) | n <- [1..] ]
        predPats              = map hsPVar predNames
        predNames             = names "p"
        compNames             = names "x"


gen                           :: (HasBaseStruct d (DI HsName e p [d] t c tp), 
                                  HasBaseStruct e (EI HsName e p [d] t c), 
                                  HasBaseStruct p (PI HsName p)) 
                              => HsConDeclI HsName t c -> d
gen (HsConDecl loc _ _ name ts) = gen' (length ts) pat loc name
  where pat compNames         = hsPApp name (map hsPVar compNames)
gen (HsRecDecl loc _ _ name fs) = gen' (length fieldNames) pat loc name
  where fieldNames              = concatMap fst fs
        pat compNames           = hsPRec name $ zipWith HsField fieldNames (map hsPVar compNames)



genLiftedCon                            :: (HasBaseStruct d (DI HsName e p [d] t c tp), HasBaseStruct e (EI HsName e p [d] t c), 
                                            HasBaseStruct p (PI HsName p)) => DI HsName e p [d] t c tp -> [d]
genLiftedCon (HsDataDecl _ _ _ ds _)    = map gen ds 
genLiftedCon (HsNewTypeDecl _ _ _ d _)  = [gen d]
genLiftedCon _                          = []


genLiftedConRec               :: Hs.HsDeclI HsName -> [Hs.HsDeclI HsName]
genLiftedConRec d             = genLiftedCon (struct d)


-- translation of imports and exports ------------------------------------------

transImps exs = map (transImp exs)
transImp exs (Prop.HsImportDecl s mn q as optspecs) =
    Hs.HsImportDecl s mn q as (fmap (transImpSpec ex) optspecs)
  where ex = applyRel (fromJust (lookup mn exs)) . getQualified . fakeSN

transImpSpec ex (hiding,ents) = (hiding,concatMap (transEnt hiding ex) ents)

transExps ex = fmap (concatMap (transExp (applyRel ex.fakeSN)))
transExp ex exp =
  case exp of
    EntE e-> map EntE (transEnt False ex e)
    _ -> [exp]

transEnt hiding rel ent =
  case ent of
    Abs i -> nub $ concatMap (absEnt hiding i) (rel i)
    ListSubs i is -> ent:[Var (predName c)|HsCon c<-is]
    _ -> [ent] -- no constrcutors/assertions/predicates on other cases

absEnt hiding i ent =
  case idTy ent of
    Assertion -> [Var (assertName i)]
    Property -> [Var (predName i)]
    ConstrOf{} | hiding -> [Abs i,Var (predName i)]
    _ -> [Abs i]

--- translation of modules -----------------------------------------------------

moduleToQC ((wm,ex),HsModule loc name exps imps decls) =
    HsModule loc name newExps newImps newDecls
  where
    newDecls = addLiftedCons . map trans . addNames $ decls
    newExps = transExps (inscpRel wm) exps
    newImps = imp "QC_combinators" True (as "QC") Nothing :
	      imp "QC_prelude" False (as "Prelude") Nothing :
	      transImps ex imps

    addNames = withSt names . mapM nameAssert
      where names = [UnQual ("unnamed_" ++ show n) | n <- [1..]]

    addLiftedCons ds  = concatMap genLiftedConRec ds ++ ds

    imp = HsImportDecl loc . PlainModule -- !!! no import from Main
    as = Just . PlainModule -- hmm


-- name all assertions
class NameAssert t i | t -> i where
  nameAssert :: t -> StateM [i] t
  
instance NameAssert (PD i pa pp) i where
  nameAssert (HsAssertion loc Nothing pa) = do n <- newName
                                               return (HsAssertion loc (Just n) pa)
  nameAssert x                            = return x

instance NameAssert (PropDecl i) i where
  nameAssert = mapMProp nameAssert nameAssert

instance (NameAssert e i, NameAssert d i) => NameAssert (DI i e p [d] t c tp) i where
  nameAssert = seqDI . mapDI return nameAssert return (mapM nameAssert) return return return 

instance (NameAssert e i, NameAssert d i) => NameAssert (EI i e p [d] t c) i where
  nameAssert = seqEI . mapEI return nameAssert return (mapM nameAssert) return return

instance NameAssert (Prop.HsDeclI i) i where nameAssert x = rec # nameAssert (struct x)
instance NameAssert (Prop.HsExpI i) i where nameAssert x = rec # nameAssert (struct x)

newName :: StateM [i] i
newName = head # updSt tail
