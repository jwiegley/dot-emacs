module C1
    (Tree, leaf1, branch1, branch2, isLeaf, isBranch,
     mkLeaf, mkBranch, myFringe, SameOrNot(..))
    where
data Tree a
    = Leaf {leaf1 :: a}
    | Branch {branch1 :: Tree a, branch2 :: Tree a}
 
mkLeaf :: a -> Tree a
 
mkLeaf = Leaf
 
mkBranch :: (Tree a) -> (Tree a) -> Tree a
 
mkBranch = Branch
 
isLeaf :: (Tree a) -> Bool
 
isLeaf (Leaf _) = True
isLeaf _ = False
 
isBranch :: (Tree a) -> Bool
 
isBranch (Branch _ _) = True
isBranch _ = False
 
sumTree :: Num a => (Tree a) -> a
 
sumTree p | isLeaf p = (leaf1 p)
sumTree p
    | isBranch p =
	(sumTree (branch1 p)) + (sumTree (branch2 p))
 
myFringe :: (Tree a) -> [a]
 
myFringe p | isLeaf p = [(leaf1 p)]
myFringe p | isBranch p = myFringe (branch1 p)
 
class SameOrNot a
  where
      isSame :: a -> a -> Bool
      isNotSame :: a -> a -> Bool
 
instance SameOrNot Int
  where
      isSame a b = a == b
      isNotSame a b = a /= b
 