module ContMT (HasCont(..), MT(..), at, Z, S, 
               removeCont, runCont, WithCont) where

import MT
import Control.Monad(liftM,MonadPlus(..))
import Control_Monad_Fix
import ImpUtils


newtype WithCont o m i = C { ($$) :: (i -> m o) -> m o }

removeCont :: WithCont o m i -> (i -> m o) -> m o
removeCont = ($$)

runCont :: Monad m => WithCont i m i -> m i
runCont k = k $$ return


--------------------------------------------------------------------------------
instance Monad m => Functor (WithCont o m) where
  fmap      = liftM

instance Monad m => Monad (WithCont o m) where
  return x  = C ($ x) 
  C m >>= f = C $ \k -> m $ \a -> f a $$ k

instance MT (WithCont o) where
  lift m    = C (m >>=)

instance MonadPlus m => MonadPlus (WithCont o m) where
    mzero             = lift mzero
    C m1 `mplus` C m2 = C $ \k -> m1 k `mplus` m2 k
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
instance HasEnv m ix e => HasEnv (WithCont o m) ix e where
  getEnv ix           = lift (getEnv ix)
  inModEnv ix f (C m) = C (inModEnv ix f . m)

instance HasState m ix s => HasState (WithCont o m) ix s where
  updSt ix            = lift . updSt ix

instance HasOutput m ix o => HasOutput (WithCont ans m) ix o where
  outputTree ix       = lift . outputTree ix

instance HasExcept m x => HasExcept (WithCont o m) x where
  raise               = lift . raise
  handle f m          = C $ \k -> handle (\x -> f x $$ k) (m $$ k)

instance Monad m => HasCont (WithCont o m) where
  callcc f            = C $ \k -> f (\a -> C $ \d -> k a) $$ k
--------------------------------------------------------------------------------


instance HasBaseMonad m n => HasBaseMonad (WithCont o m) n where
  inBase              = lift . inBase

instance HasRefs m r => HasRefs (WithCont () m) r where
  newRef      = lift . newRef
  readRef     = lift . readRef
  writeRef r  = lift . writeRef r

-- Magnus' fixpoint implementation
instance (MonadFix m, HasRefs m r) => MonadFix (WithCont () m) where
 mfix m = C $ \k -> do x <- newRef Nothing
                       let xcases j n = readRef x >>= maybe n j
                           k' b'      = xcases (const (k b')) (writeRef x (Just b'))
                       mfix $ \b -> do m b $$ k'
                                       xcases return (return (error "mfix in ContMT is bottom"))
                       xcases k (return ())

  

shift     :: Monad m => ((a -> WithCont o m o) -> WithCont o m o) -> WithCont o m a
shift f   = C (\k -> runCont $ f (\a -> C (\k' -> k' =<< k a)))

reset     :: Monad m => WithCont o m o -> WithCont o m o 
reset m   = C (\k -> k =<< runCont m)


test1           :: WithCont String IO String
test1           = do x <- reset $ do y <- shift (\f -> do z <- f "100"
                                                          f z)
                                     return ("10 + " ++ y)
                     inBase (print "hello")
                     return $ "1 + " ++ x

{-
test2           = liftM ("1 + " ++) $ reset $ liftM ("10 + " ++) $ shift (\f -> return "100")
test3           = liftM ("1 + " ++) $ reset $ liftM ("10 + " ++)  $ shift $ \f -> liftM2 (\x y -> x ++ " + " ++ y) (f "100") (f "1000")
-}
