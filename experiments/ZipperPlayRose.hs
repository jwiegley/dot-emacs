{-

Playing with Data.Tree.Zipper, to understand how they can be used to
manage a Data.Tree

-}

import Data.Tree
import Data.Tree.Zipper

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

-- ---------------------------------------------------------------------
-- Data.Tree.Zipper experimentation

f1 = r'
  where
   r = fromTree tree1
   -- r' = children r
   r' = firstChild r



------------------------------------------------------------------------
-- Utilities to show a forest/tree in ghci

df = putStrLn . drawForest
dt = putStrLn . drawTree

-- |Draw a tree using fmap
fdt ft = do
  t <- fmap drawTree ft
  putStr t




