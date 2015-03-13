module DFA where
import qualified OrdMap as OM
import MUtils(apFst,mapFst,mapSnd,collectByFst,collectBySnd,usort)
import Maybe(fromJust)

type DMap s i o = OM.OrdMap s ([(i,s)],[(o,s)])
newtype DFA s i o = DFA (DMap s i o)

---
{-
instance (Show s,Show i,Show o) => Show (DFA s i o) where
  showsPrec d (DFA m) = showsPrec d (OM.toList m)
-}

showDFA (n,DFA dfa) = "("++show n++","++showStates (OM.toList dfa)++")"
  where
    showStates = show . mapSnd (apFst collectBySnd)

---

tokenClasses x = collectBySnd . collectByFst . dfaInputEdges $ x

dfaInputEdges (DFA m) = [(e,(s,g))|(s,(is,os))<-OM.toList m,(e,g)<-is]

renumberEdges tclss (DFA ss) = DFA (fmap (apFst renEdges) ss)
  where
    renEdges is = usort $ mapFst renEdge is

    renEdge c = fromJust (OM.lookup c tcmap)

    tcmap = OM.fromList tclss


renumberStates ((start,final),DFA detm) =
    ((subst start,map subst final),
     DFA . OM.fromList . map subststate . OM.toList $ detm)
  where
    oldstate = OM.indices detm
    newstate = OM.fromList (zip oldstate [(1::Int)..])
    
    subststate (st,(iedges,oedges)) =
        (subst st,(mapSnd subst iedges,mapSnd subst oedges))

    subst st =
      case OM.lookup st newstate of
        Just s -> s
	Nothing -> error ("No mapping for "++show st)
