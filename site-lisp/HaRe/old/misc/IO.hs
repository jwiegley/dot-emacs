module IO(module IO,module PreludeIO) where
import Prelude
import PreludeIO

data IOMode      =  ReadMode | WriteMode | AppendMode | ReadWriteMode
                    deriving (Eq, Ord, {-Ix,-} Bounded, Enum, Read, Show)
data BufferMode  =  NoBuffering | LineBuffering 
                 |  BlockBuffering (Maybe Int)
                    deriving (Eq, Ord, Read, Show)
data SeekMode    =  AbsoluteSeek | RelativeSeek | SeekFromEnd
                    deriving (Eq, Ord, {-Ix,-} Bounded, Enum, Read, Show)

--- Unimplemented things:
hSetBuffering mode handle = return ()
---

data PrimHandle
instance Eq PrimHandle
instance Show PrimHandle

foreign import prim_stdin :: PrimHandle
foreign import prim_stdout :: PrimHandle
foreign import prim_stderr :: PrimHandle
foreign import primHPutChar :: PrimHandle -> Char -> IO ()
foreign import primHPutStr :: PrimHandle -> String -> IO ()
foreign import primHFlush :: PrimHandle -> IO ()

newtype Handle = Handle PrimHandle deriving (Eq,Show)

stdin = Handle prim_stdin
stdout = Handle prim_stdout
stderr = Handle prim_stderr

foreign import openFile :: FilePath -> IOMode -> IO Handle
foreign import hClose :: Handle -> IO ()
foreign import hGetLine :: Handle -> IO String
foreign import hGetContents :: Handle -> IO String

hPutChar (Handle h) c = primHPutChar h c
hPutStr (Handle h) s = primHPutStr h s
hPutStrLn h s = hPutStr h s >> hPutChar h '\n'
hPrint h x = hPutStrLn h (show x)

hFlush (Handle h) = primHFlush h

---

ioeGetErrorString (IOE k s) = s

ioErrorKind (IOE k _) = k

isEOFError e = ioErrorKind e == EOFError
isUserError e = ioErrorKind e == UserError
isDoesNotExistError e = ioErrorKind e == DoesNotExistError

---
try            :: IO a -> IO (Either IOError a)
try f          =  catch (fmap Right f) (return . Left)

bracket        :: IO a -> (a -> IO b) -> (a -> IO c) -> IO c
bracket before after m =
  do    x  <- before
        rs <- try (m x)
        after x
	returnTry rs

-- variant of the above where middle computation doesn't want x
bracket_        :: IO a -> (a -> IO b) -> IO c -> IO c
bracket_ before after m =
  do     x  <- before
         rs <- try m
         after x
	 returnTry rs

returnTry (Right r) = return r
returnTry (Left  e) = ioError e
