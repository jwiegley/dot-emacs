{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# LANGUAGE TypeOperators #-}
{-

Playing with lens zippers, to understand how they can be used to
manage a Data.Tree

-}

import Control.Applicative
import Control.Lens.Combinators
import Control.Lens.Indexed
import Control.Lens.Type
import Data.Functor.Identity
import Control.Monad

-- import Control.Applicative
import Control.Lens
import Control.Lens.Zipper
import Data.Tree
import Data.Tree.Lens


-- ---------------------------------------------------------------------

main = putStrLn "hello"

-- ---------------------------------------------------------------------

myTree = [tree1,tree2]

tree1 =
    Node "a"
      [Node "aa" []
      ,Node "ab"
         [Node "aba" []
         ,Node "abb" []
         ]
      ]

tree2 =
  Node "b"
      [Node "ba" []
      ,Node "bb" []
      ]


-- z :: Top :> Forest String
z = zipper myTree


-- Top :>> Tree a :>> a

t1 :: Forest String
t1 = z & fromWithin traverse & rightward <&> view focus

eg1 = zipper ("hello","world")
    & downward _1
    & fromWithin traverse
    & focus .~ 'J'
    & rightmost
    & focus .~ 'y'
    & rezip

{-
-- eg2 :: String
eg2 = zipper tree1
    & downward branches -- branches is in Data.Tree.Lens
    & fromWithin traverse
    & rightward
    & rezip
    -- <&> view focus
-}


-- Attempt: in tree1, go down to [aa,ab], then down to focus on aba
eg2 = zipper tree1
    & downward  branches -- focus is now [aa,ab]
    -- & fromWithin traverse & rightward
    & rightmost
    -- & focus .~ (Node "new" [])
    -- rezip
    -- <&> view focus


eg2' :: (Functor f, MonadPlus f) => f (Tree String)
eg2' = zipper tree1
    & downward  branches -- focus is now [aa,ab]
    & fromWithin traverse & rightward
    <&> focus .~ tree2
    <&> rezip

{-
*Main> fdt eg2'
a
|
+- aa
|
`- b
   |
   +- ba
   |
   `- bb
*Main>
-}


-- Look for a specific label in the subtree, and replace it
eg5 :: (Functor f, MonadPlus f) => f (Tree String)
eg5 = zipper tree1
    & downward  branches -- focus is now [aa,ab]
    & fromWithin traverse
    -- (&) :: a -> (a -> b) -> b
    & rightward
    -- & rightward
    <&> focus .~ tree2
    <&> rezip


{-
eg6 = ft
  where
    z  = zipper tree1 & downward  branches & fromWithin traverse
    ft = findSubTree z "ab"

findSubTree
  :: Zipper
        (Zipper (Zipper Top Int (Tree [Char])) Int [Tree [Char]])
        Int
        (Tree [Char])
  -> [Char]
  -> Zipper
        (Zipper (Zipper Top Int (Tree [Char])) Int [Tree [Char]])
        Int
        (Tree [Char])
-- findSubTree z w = tree1
findSubTree tr what = res
      where
        ft = tr & view focus :: Tree [Char]
        res = if (rootLabel ft == what)
          then tr
          else findSubTree (tr & rightward) what
        -- res = tr
-}

-- ------------------------
-- Data.Tree.Lens provides

-- root :: Lens' (Tree a) a
-- branches :: Lens' (Tree a) [Tree a]
--
-- The branches are a list,

eg3 :: Tree [Char]
eg3 = zipper tree1
      & downward branches
      & focus .~ [tree2]
      & rezip

-- eg4 shows tree surgery

eg4 = z1'
 where
  z1 = zipper tree1
      & downward branches
  subF = view focus z1
  z1' = z1 & focus .~ ([head subF ] ++ [tree2] ++ tail subF)
           & rezip


-- p3 = df $ view focus eg3

-- eg5 = zipper tree1 & downward branches & fromWithin traverse & rightward

-- The following generates output on ghci, as expected
-- zipper tree1 & downward branches & fromWithin traverse & rightward <&> view focus
-- Node {rootLabel = "ab", subForest = [Node {rootLabel = "aba", subForest = []},Node {rootLabel = "abb", subForest = []}]}

------------------------------------------------------------------------
-- how to search for a specific element in the tree?

-- Assumption:
--   1. the root strings are arranged in a prefix tree, i.e. all sub
--      elements have the same prefix as the parent, and the branches
--      are sorted. [as in tree1 and tree2]
--   2. the element being searched for is in fact in the tree
{-
focusOn tree key = z
 where
   z1 = zipper tree

focusOn' z key =
  let
    node = view focus z
    z' = if key == rootLabel node
         then z
         else -- find the sub tree
           where

-}

eg6:: Top :>> (Tree [Char]) :>> [(Tree [Char])]
eg6 = z1
  where
    z = zipper tree1
      & downward branches
    -- z1 = view focus z
    z1 = z




------------------------------------------------------------------------
-- Utilities to show a forest/tree in ghci

df = putStrLn . drawForest
dt = putStrLn . drawTree

-- |Draw a tree using fmap
fdt ft = do
  t <- fmap drawTree ft
  putStr t


-- --------------------------------------------------

s = ["aa","ab","ac"]

s1 = zipper s

-- ss1 = s1 & fromWithin traverse & rightward <&> view focus



-- -----------------------------------------------------------

-- from http://stackoverflow.com/questions/15489324/traversal-tree-with-lens-and-zippers

testTree = Node 1 [ Node 2 [ Node 4 [ Node 6 [], Node 8 [] ],
                             Node 5 [ Node 7 [], Node 9 [] ] ],
                    Node 3 [ Node 10 [],
                             Node 11 [] ]
                  ]

zipperTree = zipper testTree


z1 = zipperTree & downward branches
                & fromWithin traverse
                & downward root
                & focus .~ 500
                & rezip

z1' = Node 1 [ Node 500 [Node {rootLabel = 4, subForest = [Node {rootLabel = 6, subForest = []},Node {rootLabel = 8, subForest = []}]},Node {rootLabel = 5, subForest = [Node {rootLabel = 7, subForest = []},Node {rootLabel = 9, subForest = []}]}],
                       Node {rootLabel = 3, subForest = [Node {rootLabel = 10, subForest = []},Node {rootLabel = 11, subForest = []}]}]

tape = zipperTree & downward branches
                  & fromWithin traverse
                  & downward root
                  & saveTape

z2 :: Maybe (Tree Integer)
z2 = do
      t  <- (restoreTape tape testTree)
      return (t & focus .~ 15 & rezip)

z3 = zipperTree & downward branches
--                & fromWithin traverse
