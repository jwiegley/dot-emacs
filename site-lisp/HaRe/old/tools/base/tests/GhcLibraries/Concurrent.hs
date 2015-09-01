-- Dummy Concurrent module
module Concurrent where

data Chan a
data ThreadId
data MVar a

instance Show ThreadId

forkIO :: IO () -> IO ThreadId
forkIO = undefined

threadDelay :: Int -> IO ()
threadDelay = undefined

yield :: IO ()
yield = undefined

killThread :: ThreadId -> IO ()
killThread = undefined

writeChan :: Chan a -> a -> IO ()
writeChan = undefined

newChan :: IO (Chan a)
newChan = undefined

--isEmptyChan ::
isEmptyChan = undefined

--readChan ::
readChan = undefined

getChanContents :: Chan a -> IO [a]
getChanContents = undefined

newEmptyMVar :: IO (MVar a)
newEmptyMVar = undefined

newMVar :: a -> IO (MVar a)
newMVar = undefined

putMVar :: MVar a -> a -> IO ()
putMVar = undefined

readMVar :: MVar a -> IO a
readMVar = undefined

takeMVar :: MVar a -> IO a
takeMVar = undefined

swapMVar :: MVar a -> a -> IO a
swapMVar = undefined

