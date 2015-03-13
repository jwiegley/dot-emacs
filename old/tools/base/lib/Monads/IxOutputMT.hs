module IxOutputMT (HasOutput(..), MT(..), at, Z, S, Top, Under, WithOutput, 
                   removeOutput, listOutput, foldOutput, mapOutput ) where 

import MT
import Control_Monad_Fix

import Control.Monad(liftM,MonadPlus(..))
import Tree


newtype WithOutput o m a = O { unO :: m (a, Tree o) } 

-- removeOutput :: Monad m => b -> (o -> b) -> (b -> b -> b) 
--                    -> WithOutput o m a -> m (a,b)
removeOutput = unO

foldOutput empty single join (O m) = 
  do (a,t) <- m
     return (a,Tree.fold empty single join t)

listOutput :: Monad m => WithOutput o m a -> m (a,[o])
listOutput (O m) = do (a,o) <- m; return (a, Tree.toList o)

mapOutput :: Monad m => (o -> p) -> WithOutput o m a -> WithOutput p m a
mapOutput f (O m) = O $ do (a,o) <- m; return (a, fmap f o)


--------------------------------------------------------------------------------
instance Monad m => Functor (WithOutput o m) where
  fmap = liftM

instance Monad m => Monad (WithOutput o m) where
  return    = lift . return
  O m >>= f = O $ do (a,o) <- m
                     (b,p) <- unO (f a)
                     return (b, o `Tree.merge` p)

instance MT (WithOutput o) where
  lift m = O $ do x <- m; return (x, Tree.Empty)

instance MonadPlus m => MonadPlus (WithOutput o m) where
  mzero             = lift mzero
  O m1 `mplus` O m2 = O (m1 `mplus` m2)
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
instance HasEnv m ix e => HasEnv (WithOutput o m) ix e where
  getEnv ix           = lift (getEnv ix)
  inModEnv ix f (O m) = O (inModEnv ix f m)

instance HasState m ix s => HasState (WithOutput o m) ix s where
  updSt ix            = lift . updSt ix

instance Monad m => HasOutput (WithOutput o m) Z o where
  outputTree _ t      = O (return ((),t))

instance HasOutput m ix o => HasOutput (WithOutput o' m) (S ix) o where
  outputTree (Next ix) = lift . outputTree ix

instance HasExcept m x => HasExcept (WithOutput o m) x where
  raise               = lift . raise
  handle h            = O . (handle (unO . h)) . unO

instance HasCont m => HasCont (WithOutput o m) where
  callcc f            = O $ callcc $ \k -> unO $ f $ \a -> O $ k (a,Tree.Empty)

instance HasBaseMonad m n => HasBaseMonad (WithOutput o m) n where
  inBase              = lift . inBase

instance HasRefs m r => HasRefs (WithOutput o m) r where
  newRef              = lift . newRef
  readRef             = lift . readRef
  writeRef r          = lift . writeRef r

instance MonadFix m => MonadFix (WithOutput o m) where
  mfix f              = O (mfix (\ ~(a,_) -> unO (f a)))


