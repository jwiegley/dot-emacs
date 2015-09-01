module Posix where

import Prelude hiding (FilePath)
data Handler = Ignore
data DirStream
data FileStatus
type FilePath = String

--installHandler::
--sigPIPE::

installHandler = undefined
sigPIPE = undefined

openDirStream :: FilePath -> IO DirStream
openDirStream = undefined

readDirStream :: DirStream -> IO String
readDirStream = undefined

rewindDirStream :: DirStream -> IO ()
rewindDirStream = undefined

closeDirStream :: DirStream -> IO ()
closeDirStream = undefined

getFileStatus :: FilePath -> IO FileStatus
getFileStatus = undefined

isDirectory :: FileStatus -> Bool
isDirectory = undefined
