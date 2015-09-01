-- Graphs, with minimal assumptions about the nodes
module SimpleGraphs where

import Data.List(nub)
import Data.Maybe(fromMaybe)
import MUtils(collectByFst,swap)



type Graph a = [(a,[a])]
type Reachable a = [a]

graph         ::          [(a,[a])] -> Graph a
reachable     :: Eq a  => Graph a -> [a] -> Reachable a
isReachable   :: Eq a  => Reachable a -> a -> Bool
listReachable ::          Reachable a -> [a]
neighbours    :: Eq a  => Graph a ->  a  -> [a]
nodes         ::          Graph a -> [a] -- may exclude nodes without edges
edges         ::          Graph a ->        [(a,a)]
reverseGraph  :: Ord a => Graph a ->        Graph a

graph = id

-- The set of reachable nodes from a given node in a graph:
reachable graph = r []
  where
    r reached [] = reached
    r reached (s:ss) =
      if s `elem` reached
      then r reached ss
      else r (s:reached) (push (neighbours graph s) ss)

    push [] ss = ss
    push (x:xs) ss = push xs (x:ss)

-- nonreflexive:
reachable' g = reachable g . nub . concatMap (neighbours g)

isReachable xs x = x `elem` xs
listReachable = id

neighbours g n = fromMaybe [] (lookup n g)

reverseGraph g = collectByFst . map swap . edges $ g

edges g = [(from,to)|(from,ns)<-g,to<-ns]
nodes = map fst
