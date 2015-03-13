module ImpUtils (module ImpUtils, HasRefs(..)) where

import Control.Monad.ST
import Data.STRef(STRef,newSTRef,readSTRef,writeSTRef)
import Data.IORef(IORef,newIORef,readIORef,writeIORef)
import MT


instance HasBaseMonad IO IO where
  inBase    = id

instance HasRefs IO IORef where
  newRef    = newIORef
  readRef   = readIORef
  writeRef  = writeIORef

instance HasRefs (ST s) (STRef s) where
  newRef    = newSTRef
  readRef   = readSTRef
  writeRef  = writeSTRef



newPtr      :: HasRefs m r => m (r (Maybe a))
newPtr      = newRef Nothing

writePtr    :: HasRefs m r => r (Maybe a) -> a -> m ()
writePtr p  = writeRef p . Just

get         :: HasRefs m r => (o -> r b) -> o -> m b
get f       = readRef . f

set         :: HasRefs m r => (o -> r b) -> o -> b -> m ()
set f       = writeRef . f

upd         :: HasRefs m r => (o -> r b) -> (b -> b) -> o -> m ()
upd f g o   = let r = f o in writeRef r . g =<< readRef r



