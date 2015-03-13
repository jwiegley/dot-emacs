module NewSCC (sccEq,scc) where

{- A module to find strongly connected components
 - and perform a topological sort on them.
 - This is Lennart Augusstoson's code (from hbc?)
 - converted to Haskell by Iavor Diatchki.
 -}

import OpTypes
import Products((><))
import StateM
import Data.Maybe (fromJust,listToMaybe)


sccEq               :: EqOp a -> Graph a -> [Graph a]
scc                 :: Eq a => Graph a -> [Graph a]


lkpEq eq x xs = listToMaybe [ v | (k,v) <- xs, x `eq` k ]
nonfailLkpEq eq x = fromJust . lkpEq eq x

type Graph a        = [(a, [a])]
type Numbering a    = [(a, Int)]

type RW a = (Int, Numbering a, Graph a, Int)
pushMany xs (x,ns,ss,y) = (x,ns,ss ++ xs,y)
minLast m (x,ns,ss,y)   = (x,ns,ss,min y m)
getNumbering (x,ns,ss,y) = ns


sccEq eq gG = concat $ withSt [] $ mapM (g eq gG) gG
scc         = sccEq (==)


g :: EqOp a -> Graph a -> (a,[a]) -> StateM (Numbering a) [Graph a]
g eq gG vv@(v,_)   = do
    low <- getSt
    let found       = const (return [])
        notFound    = let (cs4, st) = searchC eq gG 1 low vv
                      in setSt (getNumbering st) >> return cs4
    maybe notFound found (lkpEq eq v low)




searchC :: EqOp a -> Graph a ->
            Int -> Numbering a -> (a,[a]) -> ([Graph a], RW a)
searchC eq g n low vv@(v, es)
    | nonfailLkpEq eq v low' == min' =
            (cs' ++ [nstack],
             (n', map (id >< const maxBound) nstack ++ low', [], min'))
    | otherwise = (cs', (n', low', nstack, min'))
    where
    cs'     = concat cs2
    (cs2, (n', low', nstack, min'))
        = let n1 = n + 1
              initSt = (n1, (v,n1) : low , [vv], n1)
        in withStS initSt $ mapM (f eq g) es



-- f :: EqOp a -> Graph a -> a -> StateM (RW a) [Graph a]
f eq g v = do
    (n, low, stack, min') <- getSt
    res <- case lkpEq eq v low of
        Nothing -> let (r,s) = searchC eq g n low (findVV eq g v)
                   in do setSt s; return r
        Just vm -> do setSt (n, low, [], vm); return []

    updSt (minLast min' . pushMany stack)
    return res


findVV :: EqOp a -> Graph a -> a -> (a, [a])
findVV eq g v = (v, nonfailLkpEq eq v g)



test = [('c', [])
       ,('a', ['b','c'])
       ,('b', ['a'])
       ]

test1 = [('a', "b")
        ,('c', "b")
        ,('b', "")
        ]
