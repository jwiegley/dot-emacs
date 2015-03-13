{-+
Reusable functions for translation from the (non-recursive) P-Logic structure
to Stratego.
-}

module PropStruct2Stratego2 where
import StrategoAST2 as S
import PropSyntaxStruct as P
import HsPropMaps
import HsPropPretty()
import PrettyPrint(pp)
import Maybe(fromMaybe)

transPD trId trPA trPP pd =
  case mapPD trId trPA trPP pd of
    HsPropDecl s n ns p -> property (PredDecl (PredAbs (n,map transPredParam ns),p))
    HsAssertion s (Just n) a -> assert (PropDecl (n,a))
    _ -> ignored (pp pd)
  where
    transPredParam (HsCon c) = predParam c
    transPredParam (HsVar x) = termParam x
    --predParam (HsVar x) = "Not supported: Predicate definition: values as parameters" -- !!!

transPA trId trE trT trPA trPP pa =
  case mapPA trId trE trT trPA trPP pa of
    P.Quant q i optt pa -> S.Quant ([quant q (i,t)],pa)
      where t = fromMaybe (tVar "dummy") optt
    PropApp i ts [] -> propVar i
    PropApp i ts es -> HasMult (map predArg es,predVar i) -- !!
    PropNeg a -> propNeg a
    PropOp op a1 a2 -> propOp op a1 a2
    PropEqual e1 e2 -> Equal (e1, e2)
    PropHas e p -> Has (e,p)
    PropParen a -> a
    _ -> not_supported "Assertion" pa
  where
    quant q =
      case q of
        P.All -> S.All
	Exist -> Exists

    propOp op a1 a2 =
      case op of
        P.Conj -> propConj [a1,a2]
        P.Disj -> propDisj [a1,a2]
        P.Imp  -> Implies ([a1],a2)
        P.Equiv-> S.Equiv (a1,a2)

    predArg = either id bad
    bad _ = not_supported "Predicate arguments" pa

transPP trId trE trP trT trPA trPP pred =
  case mapPP trId trE trP trT trPA trPP pred of
    PredApp i ts [] -> predVar i
    PredApp i ts ps -> DataCong (i,map transPredArg ps) -- !!!
    PredArrow p1 p2 -> Arrow (p1,p2)
    PredInfixApp p1 i p2 -> DataCong (i,map predArg [p1,p2])
    P.PredNeg optt p -> predNeg p
    PredOp op optt p1 p2 -> predOp op p1 p2
    PredLfp i _ p -> LfpPred (i,p)
    PredGfp i _ p -> GfpPred (i,p)
    PredNil -> DataCong ("[]",[])
    PredLifted e -> liftedSec e
    PredStrong p -> strong p
    PredParen p -> p
    PredComp pts a -> Comprehension (map fst pts,a)
    _ -> not_supported "Predicate" pred
  where
    transPredArg = either termArg predArg
    --bad _ = not_supported "Predicate application" "values as arguments"

    predOp op a1 a2 =
      case op of
        P.Conj -> predConj [a1,a2]
        P.Disj -> predDisj [a1,a2]
        P.Imp  -> PredImpl ([a1],a2)
        P.Equiv-> PredEquiv (a1,a2)

transQ trC trT (c:=>t) = tarrows ({-map tPred-} (trC c)) (trT t) -- ???

not_supported s x = error $ s++" not supported (yet): "++pp x
