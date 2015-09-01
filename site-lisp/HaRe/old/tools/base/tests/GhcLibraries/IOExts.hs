-- A minimal dummy IOExts module
module IOExts where

data IORef a

foreign import trace :: String -> a -> a
foreign import unsafePerformIO :: IO a -> a
foreign import unsafeInterleaveIO :: IO a -> IO a

foreign import newIORef :: a -> IO (IORef a)
foreign import readIORef :: IORef a -> IO a
foreign import writeIORef :: IORef a -> a -> IO ()

foreign import fixIO :: (a -> IO a) -> IO a


data IOArray ix el

instance Eq (IORef a)
