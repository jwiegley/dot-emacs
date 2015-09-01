{-

Playing with lens zippers, to understand how they can be used to
manage a Data.Tree

-}
import Control.Lens
import Control.Lens.Zipper
import Data.Tree
import Data.Tree.Lens

-- ---------------------------------------------------------------------

tree1 =
    Node "a"
      [Node "aa" []
      ,Node "ab"
         [Node "aba" []
         ,Node "abb" []
         ]
      ]

-- Attempt: in tree1, go down to [aa,ab], then down to focus on aba
eg2 = zipper tree1
    & downward  branches -- focus is now [aa,ab]
    & fromWithin traverse
    & rightmost

-- p2 = view focus eg2

-- ------------------------
-- Data.Tree.Lens provides

-- root :: Lens' (Tree a) a
-- branches :: Lens' (Tree a) [Tree a]
--
-- The branches are a list, 



------------------------------------------------------------------------
-- Utilities to show a forest/tree in ghci

df = putStrLn . drawForest
dt = putStrLn . drawTree
