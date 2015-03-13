{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
module MT where

import Tree

class MT t where
  lift :: (Monad m, Monad (t m)) => m a -> t m a

{-
class MapMT t where
  mapMT :: (Monad m, Monad n) => (forall a. m a -> n a) -> t m a -> t n a
-}
data Z
newtype S n = Next n

at    = undefined
this  = at::Z


type Top    = Z
type Under  = S


-- Properties are written in a style like the one described 
-- in the paper "Evaluation Logics" by Andy Pitts


-- properties are not exhaustive, they are just things that came to mind /Iavor


--------------------------------------------------------------------------------
class Monad m => HasEnv m ix e | m ix -> e where
  getEnv    :: ix -> m e
  inEnv     :: ix -> e -> m a -> m a
  inModEnv  :: ix -> (e -> e) -> m a -> m a

  inEnv ix e       = inModEnv ix (const e)
  inModEnv ix f m  = do e <- getEnv ix; inEnv ix (f e) m

  -- define at least one of:
  --  * getEnv, inEnv
  --  * getEnv, inModEnv

  -- properties:

  -- getEnv ix >> m = m

  -- [ x <- getEnv
  --   y <- m 
  --   z <- getEnv ] (x == z)

  -- inModEnv ix f getEnv = fmap f (getEnv ix)

--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
class Monad m => HasState m ix s | m ix -> s where
  updSt   :: ix -> (s -> s) -> m s
  updSt_  :: ix -> (s -> s) -> m () 
  getSt   :: ix -> m s
  setSt   :: ix -> s -> m s
  setSt_  :: ix -> s -> m ()
  
  updSt ix f  = do s <- getSt ix; setSt ix (f s)
  setSt ix    = updSt ix . const
  getSt ix    = updSt ix id

  updSt_ ix f = do updSt ix f; return ()
  setSt_ ix s = do setSt ix s; return ()

  -- define at least one of:
  --  * updSt
  --  * getSt, setSt

  -- properties:

  -- getSt ix >> m = m

  -- [ x <- getSt ix
  --   y <- updSt ix f ] (x = y)

  -- [ x <- getSt ix 
  --   y <- updSt ix f
  --   z <- getSt ix ] (z = f x)
 

--------------------------------------------------------------------------------

  
--------------------------------------------------------------------------------
class Monad m => HasOutput m ix o | m ix -> o where
  output      :: ix -> o -> m ()
  outputs     :: ix -> [o] -> m ()
  outputTree  :: ix -> Tree o -> m ()   

  output ix   = outputTree ix . Tree.Single
  outputs ix  = mapM_ (output ix)

  outputTree ix Tree.Empty      = return ()
  outputTree ix (Tree.Single x) = output ix x
  outputTree ix (Tree.Node x y) = outputTree ix x >> outputTree ix y

  -- define at least one of:
  -- * outputTree
  -- * output

  
--------------------------------------------------------------------------------



--------------------------------------------------------------------------------
class Monad m => HasExcept m x | m -> x where
  raise   :: x -> m a
  handle  :: (x -> m a) -> m a -> m a

  -- define at least one of:
  --  * raise, handle


-- m `catch` h = handle h m

instance HasExcept Maybe () where
  raise _           = Nothing
  handle h Nothing  = h ()
  handle h x        = x
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
class Monad m => HasCont m where
  callcc :: ((a -> m b) -> m a) -> m a
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
class (Monad m, Monad n) => HasBaseMonad m n | m -> n where
  inBase :: n a -> m a
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
class Monad m => HasRefs m r | m -> r where
  newRef    :: a -> m (r a)
  readRef   :: r a -> m a
  writeRef  :: r a -> a -> m ()
--------------------------------------------------------------------------------




