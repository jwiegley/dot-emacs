module FreeNamesPropStruct where
import FreeNames
import DefinedNames(DefinedNames)
import PropSyntaxStruct
import HsIdent
import Lists((\\\))

-- !!! Predicates are treated as constructors, which is probably not useful...

instance (Eq i,FreeNames i pa,FreeNames i pp) => FreeNames i (PD i pa pp) where
  freeNames (HsAssertion s optn pa) = filter (not.istyvar) (freeNames pa)
  freeNames (HsPropDecl s n ns pp) =
      filter (not.istyvar) (freeNames pp \\\ map val ns)
			  -- Assuming property declarations are recursive

instance (Eq i,FreeNames i e,FreeNames i t,FreeNames i pa,FreeNames i pp)
       => FreeNames i (PA i e t pa pp) where
  freeNames a =
    case a of
      Quant q i optt a -> freeNames optt ++ (freeNames a \\\ [var i])
--    PropId i ->  [val (HsCon i)]
      PropApp i ts e -> con i:freeNames (ts,e)
      PropNeg a -> freeNames a
      PropOp _ a1 a2 -> freeNames (a1,a2)
      PropEqual e1 e2 -> freeNames (e1,e2)
      PropHas e p -> freeNames (e,p) -- !!
      PropParen pa -> freeNames pa
--    PropLambda i pa -> freeNames pa \\\ [var i]
--    PropLet i optt e pa -> freeNames (optt,e)++(freeNames pa\\\ [var i])

instance (Eq i,FreeNames i e,FreeNames i p,FreeNames i t,
	  DefinedNames i p,
	  FreeNames i pa,FreeNames i pp)
      => FreeNames i (PP i e p t pa pp) where
  freeNames p =
    case p of
--    PredId i -> [val (HsCon i)]
      PredApp i ts p -> con i:freeNames (ts,p)
      PredArrow p1 p2 -> freeNames (p1,p2)
      PredInfixApp p1 i p2 -> con i:freeNames (p1,p2)
      PredNeg optt a -> freeNames (optt,a)
      PredOp _ optt a1 a2 -> freeNames (optt,a1,a2)
      PredLfp i optt p -> freeNames (p,optt)\\\[con i]
      PredGfp i optt p -> freeNames (p,optt)\\\[con i]
      PredNil -> []
      PredLifted e -> freeNames e
      PredStrong p -> freeNames p
      PredParen p -> freeNames p
      PredComp pts a -> freeNames ps ++ (freeNames a \\\ defs ps)
         where ps = map fst pts

instance (FreeNames i c,FreeNames i t) => FreeNames i (Q c t) where
   freeNames (c:=>t) = freeNames (c,t)
