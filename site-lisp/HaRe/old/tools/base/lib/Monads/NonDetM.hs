module NonDetM (NonDetM, withStrat) where

import Tree
import Control.Monad
import MT
import Control_Monad_Fix

newtype NonDetM a     = ND { unND :: Tree a }

withStrat            :: (Tree a -> b) -> NonDetM a -> b
withStrat f (ND m)    = f m


instance Functor NonDetM where
  fmap                = liftM

instance Monad NonDetM where
  return x            = ND (return x)
  ND m >>= f          = ND (m >>= unND . f)

instance MonadPlus NonDetM where
  mzero               = ND mzero
  mplus (ND x) (ND y) = ND (mplus x y)

instance HasBaseMonad NonDetM NonDetM where
  inBase              = id

instance MonadFix NonDetM where
  mfix f                = ND (mfix (unND . f))




