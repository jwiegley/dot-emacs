module GraphOps where
import qualified IntMap as M
import qualified IntSet as S
--import ListUtil(mapSnd)
--import Collect

---- Various functions on directed graphs (or relations if you wish)

-- A graph is represented as a finite map from nodes to set of nodes,
type Graph = M.IntMap NodeSet
-- and nodes are represented by numbers.
type Node = Int
type NodeSet = S.IntSet

--------------------------------------------------------------------------------
neighbours        :: Graph -> Node -> NodeSet
neighbourlist     :: Graph -> Node -> [Node]
reachable         :: Graph -> Node -> NodeSet
transitiveClosure :: Graph -> Graph
nodes             :: Graph -> [Node]
scc               :: Graph -> [[Node]]
--------------------------------------------------------------------------------

-- The neighbours of a node:
neighbours g = M.lookupWithDefault g S.empty 
neighbourlist g = S.toList . neighbours g 

-- The set of reachable nodes from a given node in a graph:
reachable graph start = r S.empty [start]
  where
    r reached [] = reached
    r reached (s:ss) =
      if s `S.elem` reached
      then r reached ss
      else r (S.add s reached) (push (neighbourlist graph s) ss)

    push [] ss = ss
    push (x:xs) ss = push xs (x:ss)

-- The reflexitive, transitive closure of a graph (relation):
transitiveClosure graph = 
  M.fromList . map (\s->(s,reachable graph s)) . nodes $ graph

-- Reverse all the edges in a graph
--converse = neighbourtable . map swap . edgelist

-- Represenation changes:
--edgelist graph = [(from,to)|(from,tos)<-M.toList graph,to<-S.toList tos]
--neighbourtable = M.fromList . mapSnd S.fromList . collectByFst

-- List the nodes in a graph:
nodes = map fst . M.toList


-- Strongly Connected Components (equivalence classes):
scc graph = sc S.empty (nodes graph)
  where
    tg = transitiveClosure graph

    sc visited [] = []
    sc visited (n:ns) =
       case n `S.elem` visited of
         True -> sc visited ns
	 False -> if null scc0 then sc visited' ns else scc1:sc visited' ns
	   where
	     visited' = S.union visited (S.fromList scc1)
	     scc1 = n:scc0
	     scc0 = [n' | n' <- forward, n'/=n, n `S.elem` neighbours tg n']
	     forward = neighbourlist tg n
