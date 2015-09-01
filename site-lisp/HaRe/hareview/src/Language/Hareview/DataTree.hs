module Language.Hareview.DataTree where

-- syb
import Data.Generics (Data
                     ,extQ
                     ,gmapQ
                     ,showConstr
                     ,toConstr)

-- containers
import Data.Tree (Tree(Node,rootLabel))

-- | Trealise Data to Tree (from SYB 2, sec. 3.4 )
data2tree :: Data a => a -> Tree String
data2tree = gdefault `extQ` atString
  where 
    atString x = Node x []
    gdefault x = Node (showConstr $ toConstr x) (gmapQ data2tree x) 
    
flat :: Tree String -> Tree String
flat = id -- do nothing, see commentary below





{- -- try to flatten degenerated trees (lists of cons)


flat (Node a xs) = Node a xs --(flat <$> (children False =<< xs))    

-- use a boolean marker to notice whether we are inside a list (True) 
-- or should start a new list, then recurse
children :: Bool -> Tree String -> [Tree String]
children False (Node "(:)" [left,right])        = [Node ("ListOf"++(rootLabel left)) (left:(children True right)) ]
children True  (Node "(:)" [left,Node "[]" []]) = [left]
children True  (Node "(:)" [left,right])        = left:(children True right)
children _ (Node a xs) 
 | null xs  =  [Node a []]
 |otherwise =  [Node a xs]
children x y = error ("No pattern match for children " ++ show x ++ " " ++ (drawTree y))
-}
