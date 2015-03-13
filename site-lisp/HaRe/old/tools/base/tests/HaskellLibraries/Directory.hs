module Directory where
import Prelude
import Time(ClockTime)

data Permissions
  = Permissions { readable, writable, executable, searchable :: Bool }
  deriving ( Eq, Ord, Read, Show )

foreign import createDirectory :: FilePath -> IO ()
foreign import removeDirectory :: FilePath -> IO ()
foreign import removeFile :: FilePath -> IO ()
foreign import renameDirectory  :: FilePath -> FilePath -> IO ()
foreign import renameFile  :: FilePath -> FilePath -> IO ()

foreign import getDirectoryContents  :: FilePath -> IO [FilePath]
foreign import getCurrentDirectory  :: IO FilePath
foreign import setCurrentDirectory  :: FilePath -> IO ()

foreign import doesFileExist :: FilePath -> IO Bool
foreign import doesDirectoryExist :: FilePath -> IO Bool

foreign import getPermissions :: FilePath -> IO Permissions
foreign import setPermissions :: FilePath -> Permissions -> IO ()

foreign import getModificationTime :: FilePath -> IO ClockTime
