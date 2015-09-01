module Tree where 

import Control.Monad
import Prelude hiding (sequence)    -- doesn't work in Hugs.
import Control_Monad_Fix


data Tree a           = Empty | Single { theSingle :: a } | Node { theLeft :: Tree a, theRight :: Tree a }
                          deriving Show

merge Empty t         = t
merge t Empty         = t
merge t1 t2           = Node t1 t2

fold e s n            = f
  where f Empty       = e
        f (Single a)  = s a
        f (Node l r)  = n (f l) (f r)

toList x              = fold id (:) (.) x []


assertEmpty t         = Empty
assertSingle t        = Single (theSingle t)
assertNode t          = Node (theLeft t) (theRight t)


instance Functor Tree where
  fmap                = liftM


instance Monad Tree where
  return              = Single
  Empty    >>= f      = Empty
  Single a >>= f      = f a
  Node x y >>= f      = Node (x >>= f) (y >>= f) 

    
instance MonadPlus Tree where        
  mzero               = Empty
  mplus               = Node

instance MonadFix Tree where
  mfix f                  = obs result
    where result          = f (theSingle result)
          obs (Node _ _)  = Node (mfix (theLeft . f)) (mfix (theRight . f))
          obs x           = x




-- left to right
sequence             :: Monad m => Tree (m a) -> m (Tree a)
sequence              = fold (return Empty) (liftM Single) (liftM2 Node)

mapM f                = Tree.sequence . fmap f

