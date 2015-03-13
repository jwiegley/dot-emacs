-- A dummy ST module
module ST where

data ST s a     = ST
data STRef s a = STRef

foreign import newSTRef :: a -> ST s (STRef s a)
foreign import readSTRef :: STRef s a -> ST s a
foreign import writeSTRef :: STRef s a -> a -> ST s ()

foreign import fixST :: (a -> ST s a) -> ST s a

instance Eq (STRef s a)
instance Functor (ST s)
instance Monad (ST s)
