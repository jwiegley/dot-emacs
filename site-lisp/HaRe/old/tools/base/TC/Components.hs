module Components where

import Syntax
import Scope
import List((\\))
-- import LazyST

getAllNames (HsModule _ _ _ ds) = 
    let boundNames = map (map fst . varNames) (map names ds)
	fvNames    = map freeVarsDecl ds
    in
        (boundNames, fvNames, zipWith (\\) fvNames boundNames)


freeVarsExp (Exp e) = freeVarsE freeVarsExp e

freeVarsDecl (Dec d) = freeVarsD freeVarsDecl freeVarsExp d

-- dif === (\\), provided the argument lists don't contain duplicates.
{-
dif [] _ = []
dif (x:xs) ys = if (x `elem` ys) then dif xs ys else x : (dif xs ys)
-}

{-
type Vertex  = Int

-- Representing graphs:

type Table a = [(Vertex, a)]
type Graph   = Table [Vertex]

vertices :: Graph -> [Vertex]
vertices  = map fst graph

type Edge = (Vertex, Vertex)

aat tab v = case List.find (\ (x,y) -> x == v) tab of Just (_,r) -> r
indices tab = map fst tab

edges    :: Graph -> [Edge]
edges g   = [ (v, w) | v <- vertices g, w <- g `aat` v ]

mapTr    :: (Vertex -> a -> b) -> Table a -> Table b
mapTr f t = [ (v, f v (t `aat` v)) | v <- indices t ]

type Bounds = (Vertex, Vertex)

outdegree :: Graph -> Table Int
outdegree  = mapTr numEdges
             where numEdges v ws = length ws

buildG :: Bounds -> [Edge] -> Graph
buildG _ [] = []
buildG _ (x:xs) = 

graph = buildG (1,10)
         (reverse
          [ (1, 2),  (1, 6),  (2, 3),
            (2, 5),  (3, 1),  (3, 4),
            (5, 4),  (7, 8),  (7, 10),
            (8, 6),  (8, 9),  (8, 10) ]
         )
         
-- Depth-first search

-- Specification and implementation of depth-first search:

data Tree a   = Node a (Forest a) deriving Show
type Forest a = [Tree a]

nodesTree (Node a f) ans = nodesForest f (a:ans)
nodesForest [] ans = ans
nodesForest (t : f) ans = nodesTree t (nodesForest f ans)

dff          :: Graph -> Forest Vertex
dff g         = dfs g (vertices g)

dfs          :: Graph -> [Vertex] -> Forest Vertex
dfs g vs      = prune (bounds g) (map (generate g) vs)

generate     :: Graph -> Vertex -> Tree Vertex
generate g v  = Node v (map (generate g) (g `aat` v))


type Set s    = STArray s Vertex Bool

mkEmpty      :: Bounds -> ST s (Set s)
mkEmpty bnds  = newSTArray bnds False

contains     :: Set s -> Vertex -> ST s Bool
contains m v  = readSTArray m v

include      :: Set s -> Vertex -> ST s ()
include m v   = writeSTArray m v True

prune        :: Bounds -> Forest Vertex -> Forest Vertex
prune bnds ts = runST (mkEmpty bnds >>= \m ->
                       chop m ts)

chop         :: Set s -> Forest Vertex -> ST s (Forest Vertex)
chop m []     = return []
chop m (Node v ts : us)
              = contains m v >>= \visited ->
                if visited then
                  chop m us
                else
                  include m v >>= \_  ->
                  chop m ts   >>= \as ->
                  chop m us   >>= \bs ->
                  return (Node v as : bs)
         
-- Algorithm 2: topological sorting

postorder :: Tree a -> [a]
postorder (Node a ts) = postorderF ts ++ [a]

postorderF   :: Forest a -> [a]
postorderF ts = concat (map postorder ts)

postOrd      :: Graph -> [Vertex]
postOrd       = postorderF . dff

--topSort      :: Graph -> [Vertex]
--topSort       = reverse . postOrd   

-- Algorithm 4: strongly connected components

reverseE    :: Graph -> [Edge]
reverseE g   = [ (w, v) | (v, w) <- edges g ]

transposeG  :: Graph -> Graph
transposeG g = buildG (bounds g) (reverseE g)

scc          :: Graph -> Forest Vertex
scc g         = dfs (transposeG g) (reverse (postOrd g))
 
scc2 g = reverse (map (\ t -> nodesTree t []) (scc graph))
-}
