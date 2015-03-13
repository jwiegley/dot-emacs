module PreludeIO {-(
    FilePath, IOError(..), ioError, userError, catch,
    putChar, putStr, putStrLn, print,
    getChar, getLine, getContents, interact,
    readFile, writeFile, appendFile, readIO, readLn
  )-} where

import PreludeBuiltin

type  FilePath = String

data IOErrorKind
  = EOFError          
  | OtherError
  | UserError
  | AlreadyExistsError 
  | DoesNotExistError 
  | AlreadyInUseError 
  | FullError         
  | IllegalOperation  
  | PermissionError   
  deriving (Eq)
--instance Eq IOErrorKind

-- The internals of this type are system dependent:
data IOError = IOE IOErrorKind String --deriving (Eq)

instance  Show IOError  --where ...
instance  Eq IOError  --where ...

ioError          ::  IOError -> IO a
ioError          =   undefined--primIOError

userError        ::  String -> IOError
userError        =   IOE UserError

catch            ::  IO a -> (IOError -> IO a) -> IO a
catch            =   undefined--primCatch

putChar          :: Char -> IO ()
putChar          =  undefined--primPutChar

putStr           :: String -> IO ()
putStr s         =  mapM_ putChar s

putStrLn         :: String -> IO ()
putStrLn s       =  do putStr s
                       putStr "\n"

print            :: Show a => a -> IO ()
print x          =  putStrLn (show x)

getChar          :: IO Char
getChar          =  undefined--primGetChar

getLine          :: IO String
getLine          =  do c <- getChar
                       if c == '\n' then return "" else
                          do s <- getLine
                             return (c:s)


foreign import getContents      :: IO String
foreign import readFile         :: FilePath -> IO String
foreign import writeFile        :: FilePath -> String -> IO ()
foreign import appendFile       :: FilePath -> String -> IO ()

interact         ::  (String -> String) -> IO ()
interact f       =  do s <- getContents
                       putStr (f s)


  -- raises an exception instead of an error

readIO   :: Read a => String -> IO a
readIO s =  case [x | (x,t) <- reads s, ("","") <- lex t] of
              [x] -> return x
              []  -> ioError (userError "Prelude.readIO: no parse")
              _   -> ioError (userError "Prelude.readIO: ambiguous parse")

readLn           :: Read a => IO a
readLn           =  do l <- getLine
                       r <- readIO l
                       return r
