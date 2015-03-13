-- $Id: SCC.hs,v 1.10 2001/07/30 19:02:20 moran Exp $

module SCC where

import Scope(freeD)
import ST
import List
import qualified Array as A
import Syntax

subgraph nodes g =
  let es = edges g
      f (x,y) = elem x nodes && elem y nodes
      es' = filter f es
      n = (length nodes) - 1
      bounds = (0,n)
      pairs = zip nodes [0..]
      encode x = case find (\ (a,b) -> a==x) pairs of Just(a,b) -> b
      decode x = case find (\ (a,b) -> b==x) pairs of Just(a,b) -> a
      trans (x,y) = (encode x, encode y)
      g' = buildG bounds (map trans es')
  in g'
  
hascycle nodes g =
  any (\ x -> length x >1) (scc2 (subgraph nodes g))

---------------------------------------------
bindingGroups :: [HsDecl] -> ([[HsDecl]],Bool)
bindingGroups ds = 
   let graph = makeGraph ds
       topsort = SCC.scc2 graph
       f group = map (\x -> ds!!x) group
       groups = map f topsort
       
       isSynonym (Dec (HsTypeDecl _ _ _)) = True
       isSynonym _ = False
       bs = map isSynonym ds
       isSyn n = bs !! n
       nodes = filter isSyn (indices graph)
       syngraph = subgraph nodes graph
   in (groups,hascycle nodes syngraph)



tim = bindingGroups       
------------------------------------------
-- f x = 2 + (g x)
-- g y = (f y) - y
-- z = t
-- t = t
-- qq  = y
-- m = (t,n) + (g n, t n)

makeGraph ds =
  let (boundf,_) = freeD ds  
      
      get x = let (boundf,freef) = freeD [x]
                
              in (boundf [],        -- names defined in each d
                  nub(freef []))    -- d depends upon these
      freelist = map get ds        
      bound = nub(boundf [])        -- [f,g,z,t,qq,m]
      restrict (defined,free) = (defined,intersect free bound) 
      pairs = map restrict freelist -- [([f],[g]),([g],[f]),([z],[t]),
                                    --  ([t],[]),([qq],[]),([m],[t,g])] 
      loc x = loc' x pairs 0
      loc' x ((def,f):xs) n = if elem x def then n else loc' x xs (n+1)
      edge (def,free) n = (n,n) : (map (\ f -> (n,loc f)) free)
      edges = concat (zipWith edge pairs [0..])
      bounds = (0,(length ds) - 1)
  in (buildG bounds edges)

vars ds = zip (map (\ (f1,f2) -> (f1 [], f2 [])) $ map (\x -> freeD [x]) ds) [0..]

boundIn :: HsName -> [( ([HsName],[HsName]), Int)] -> Int
boundIn n [] =  -1 --error ("Variable " ++ (show n) ++ " not bound anywhere!!!")
boundIn n ( ((bounds,frees),dnum) : rest) = 
        if n `elem` bounds 
           then dnum
           else boundIn n rest

buildGraph ::  [(([HsName],[HsName]),Int)] ->  [(([HsName],[HsName]),Int)] -> [(Int,Int)]
buildGraph ds [] = []
buildGraph ds (((bounds,frees),bnum):rest) =
    (bnum,bnum) : [ (bnum,x ) | x <- map (\n -> boundIn n ds) frees ] ++ (buildGraph ds rest)

depgraph ds = 
   (buildG (-1, (length ds) - 1) $ 
         ((reverse (buildGraph (vars ds) (vars ds) ))) )




type Vertex  = Int

-- Representing graphs:

type Table a = A.Array Vertex a -- [(Vertex, a)]
type Graph   = Table [Vertex]

vertices :: Graph -> [Vertex]
vertices graph  = A.indices graph -- (map fst . A.assocs) graph

type Edge = (Vertex, Vertex)

--aat tab v = case List.find (\ (x,y) -> x == v) (A.assocs tab) of Just (_,r) -> r
aat tab v = tab A.! v
indices tab = A.indices tab

edges    :: Graph -> [Edge]
edges g   = [ (v, w) | v <- vertices g, w <- g `aat` v ]

mapTr    :: (Vertex -> a -> b) -> Table a -> Table b
mapTr f t = A.array (A.bounds t) [ (v, f v (t `aat` v)) | v <- indices t ]

type Bounds = (Vertex, Vertex)

outdegree :: Graph -> Table Int
outdegree  = mapTr numEdges
             where numEdges v ws = length ws

buildG :: Bounds -> [Edge] -> Graph
--buildG _ [] = []
--buildG _ (x:xs) =  []
buildG bnds edges = A.accumArray (flip (:)) [] bnds edges


graph = buildG (1,10)
         (reverse
          [ (1, 2),  (1, 6),  (2, 3),
            (2, 5),  (3, 1),  (3, 4),
            (5, 4),  (7, 8),  (7, 10),
            (8, 6),  (8, 9),  (8, 10) ]
         )
         
-- Depth-first search

-- Specification and implementation of depth-first search:

data Tree a   = Node a (Forest a) -- deriving Show
type Forest a = [Tree a]

instance Show a => Show (Tree a) where
   show (Node a []) = (show a)
   show (Node a as) = (show a) ++ "" ++ (showList as "") ++ ""


nodesTree (Node a f) ans = nodesForest f (a:ans)
nodesForest [] ans = ans
nodesForest (t : f) ans = nodesTree t (nodesForest f ans)

dff          :: Graph -> Forest Vertex
dff g         = dfs g (vertices g)

dfs          :: Graph -> [Vertex] -> Forest Vertex
dfs g vs      = prune (A.bounds g) (map (generate g) vs)

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
transposeG g = buildG (A.bounds g) (reverseE g)

scc          :: Graph -> Forest Vertex
scc g         = dfs (transposeG g) (reverse (postOrd g))
 
scc2 g = reverse (map (\ t -> nodesTree t []) (scc g))
