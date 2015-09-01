module PosixProcEnv where

data SysVar = ArgumentLimit | ChildLimit | ClockTick | GroupLimit | OpenFileLimit | PosixVersion | HasSavedIDs | HasJobControl

data ProcessTimes -- (PosixUtil.ClockTick, PrelByteArr.ByteArray Int)
type ClockTick = Int -- from PosixUtil

foreign import getProcessTimes :: IO ProcessTimes
foreign import elapsedTime :: ProcessTimes -> ClockTick
