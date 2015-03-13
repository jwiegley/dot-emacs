-- Dummy LazyST module
module LazyST where

data ST s a
data STRef s a

foreign import newSTRef :: a -> ST s (STRef s a)
foreign import readSTRef :: STRef s a -> ST s a
foreign import writeSTRef :: STRef s a -> a -> ST s a

foreign import fixST :: (a -> ST s a) -> ST s a
