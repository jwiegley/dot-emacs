module NonDetMT (WithNonDet, removeNonDet) where

import Tree
import Control.Monad
import MT
import Control_Monad_Fix

newtype WithNonDet m a  = ND { removeNonDet :: m (Tree a) }


instance Monad m => Functor (WithNonDet m) where
  fmap                  = liftM

instance Monad m => Monad (WithNonDet m) where
  return x              = ND (return (return x))
  ND m >>= f            = ND (liftM join . Tree.mapM (removeNonDet . f) =<< m)

instance MT WithNonDet where
  lift m                = ND (liftM return m)

instance Monad m => MonadPlus (WithNonDet m) where
  mzero                 = ND (return mzero)
  mplus (ND x) (ND y)   = ND (liftM2 mplus x y)



instance HasEnv m ix e => HasEnv (WithNonDet m) ix e where
  getEnv                = lift . getEnv 
  inModEnv ix f (ND m)  = ND (inModEnv ix f m)

instance HasState m ix s => HasState (WithNonDet m) ix s where
  updSt ix              = lift . updSt ix 

instance HasOutput m ix o => HasOutput (WithNonDet m) ix o where
  outputTree ix         = lift . outputTree ix 

instance HasExcept m x => HasExcept (WithNonDet m) x where
  raise                 = lift . raise 
  handle h (ND m)       = ND (handle (removeNonDet . h) m)

instance HasCont m => HasCont (WithNonDet m) where
  callcc f              = ND $ callcc $ \k -> removeNonDet $ f $ ND . k . return 

instance HasBaseMonad m n => HasBaseMonad (WithNonDet m) n where
  inBase                = lift . inBase

instance HasRefs m r => HasRefs (WithNonDet m) r where
  newRef                = lift . newRef
  readRef               = lift . readRef
  writeRef r            = lift . writeRef r

instance MonadFix m => MonadFix (WithNonDet m) where
  mfix f                = ND $ do res <- mfix (removeNonDet . f . theSingle)
                                  case res of
                                    Node _ _ -> do l <- removeNonDet $ mfix (ND . liftM theLeft . removeNonDet . f)
                                                   r <- removeNonDet $ mfix (ND . liftM theRight . removeNonDet . f)
                                                   return (Node l r)
                                    _        -> return res
         

        



