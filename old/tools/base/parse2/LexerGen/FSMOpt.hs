module FSMOpt where
import FSM
import GraphOps
import MUtils(collectByFst,collectBySnd,mapFst,mapSnd,usort)
import qualified IntMap as M
import qualified IntSet as S
import qualified OrdMap as OM
import List(sort,partition)

rmeqstate (n,NFA m) = (n',NFA (M.fromList m'))
  where (n',m') = repeat' rmeqstate1 (n,M.toList m)

repeat' f x =
  case f x of
    (True,x') -> x'
    (False,x') -> repeat' f x'

rmeqstate1 ((st,go),m) = (null sml,((s st,s go), m3))
  where
    m3 = [(st,[(e,s go)|(e,go)<-es])|(st:_,es)<-m2b]
    s x= M.lookupWithDefault sm x x
    sm = M.fromList sml
    sml = smla++smlb
    smlb = [(old,new)|(new:ss,_)<-m2b,old<-ss]
    smla = [(old,new)|(olds,[(E,new)])<-m2a,old<-olds]
    (m2a,m2b) = partition jumpstate m2
    m2 = opt m

    jumpstate (ss,[(E,g)]) = True
    jumpstate _ = False

    opt = collectBySnd . mapSnd usort

connectivity (n,NFA m) = (n,fmap next m)
  where next = S.fromList . map snd

epsilonconnectivity m = fmap epsnext m
  where epsnext ns = S.fromList [s|(E,s)<-ns]

unreachable fsm = sort . S.toList $ all `S.minus` r
  where
    r = reachable g start
    all = S.fromList . map fst . M.toList $ g
    ((start,_),g) = connectivity fsm

tokenclasses x = collectBySnd . collectByFst . tokenedges . edges $x

tokenedges edges = [(i,sg)|(T (I i),sg)<-edges]
outputedges edges = [(o,sg)|(T (O o),sg)<-edges]
epsilonedges edges = [sg|(E,sg)<-edges]

edges (NFA m) = [(e,(s,g))|(s,es)<-M.toList m,(e,g)<-es]

renumberEdges tclss (NFA ss) = NFA (fmap (usort . mapFst renEdge) ss)
  where
    renEdge (T (I c)) = case OM.lookup c tcmap of Just i -> T (I i)
    renEdge (T (O x)) = T (O x)
    renEdge E = E
    tcmap = OM.fromList tclss
