{-+
This module defines a number of classes that captures various forms of IO.
This allows code to specify IO operations without being tied directly to
the standard #IO# monad.

Instances for the standard #IO# type as well as for all monad transformers
(for all classes except one) are provided. This allows the IO operations to
be used without explicit lifting in monads that extend the IO monad by
an arbitrary number of monad transformers.

Note that we redefine some functions exported from the #Prelude#. To be able
to use these, you need to refer to them by a qualified name, or exclude the
Prelude functions from the unqualified name space by explicitly importing
the #Prelude# and hiding them (as shown below, for example).

By the way, it *is* annoying that #Functor# isn't a superclass of
 #Monad#, isn't it!
-}
module AbstractIO(module AbstractIO,
		  IOError,ClockTime,S.ExitCode(..)) where
import Prelude hiding (readFile,writeFile,
		       putStr,putStrLn,print,
		       getLine,readLn,getContents,
		       catch,ioError,userError)
import qualified Prelude
import qualified Directory as D
import qualified System as S
import qualified IO
import qualified Time
import Time(ClockTime,CalendarTime)
import MT(MT(..))

{-+
Reading and writing files
-------------------------
-}
class (Functor io,Monad io) => FileIO io where
  readFile :: FilePath -> io String
  writeFile :: FilePath -> String -> io ()

instance FileIO IO where
  readFile = Prelude.readFile
  writeFile = Prelude.writeFile

instance (MT t,Functor (t m),Monad (t m),FileIO m) => FileIO (t m) where
  readFile             = lift . readFile
  writeFile path       = lift . writeFile path


{-+
Standard IO
-----------
(For messages in the terminal window and user input.)
-}
class (Functor io,Monad io) => StdIO io where
  putStr,putStrLn,ePutStr,ePutStrLn :: String -> io ()
  -- getLine :: io String -- blocking IO is considered bad by some... :-)
  getContents :: io String

  putStrLn s = putStr s >> putStr "\n"
  ePutStrLn s = ePutStr s >> ePutStr "\n"

print x = putStrLn (show x)

readIO s =  case [x | (x,t) <- reads s, ("","") <- lex t] of
              [x] -> return x
              []  -> ioError (userError "Prelude.readIO: no parse")
              _   -> ioError (userError "Prelude.readIO: ambiguous parse")

instance StdIO IO where
  putStr    = Prelude.putStr
  putStrLn  = Prelude.putStrLn
  ePutStr   = IO.hPutStr IO.stderr
  ePutStrLn = IO.hPutStrLn IO.stderr
  -- getLine  = Prelude.getLine
  getContents = Prelude.getContents

instance (MT t,Functor (t m),Monad (t m),StdIO m) => StdIO (t m) where
  putStr   = lift . putStr
  putStrLn = lift . putStrLn
  ePutStr   = lift . ePutStr
  ePutStrLn = lift . ePutStrLn
  -- getLine  = lift getLine
  getContents = lift getContents

{-+
System interaction
------------------
Operations corresponding to the standard library module #System#.
(Executing shell commands and other interaction with command line shells.)
-}


class (Functor io,Monad io) => SystemIO io where
  system :: String -> io S.ExitCode
  getEnv :: String -> io String
  getProgName :: io String
  getArgs :: io [String]
  -- ... exitWith

instance SystemIO IO where
  system = S.system
  getEnv = S.getEnv
  getProgName = S.getProgName
  getArgs = S.getArgs

instance (MT t,Functor (t m),Monad (t m),SystemIO m) => SystemIO (t m) where
  system = lift . system
  getEnv = lift . getEnv
  getProgName = lift getProgName
  getArgs = lift getArgs

{-+
Directory manipulation
----------------------
Operations corresponding to the standard library module #Directory#.
-}

class (Functor io,Monad io) => DirectoryIO io where
  createDirectory,removeFile :: FilePath -> io ()
  getModificationTime :: FilePath -> io ClockTime
  doesFileExist, doesDirectoryExist :: FilePath -> io Bool
  getDirectoryContents :: FilePath -> io [FilePath]

-- Base case:
instance DirectoryIO IO where
  createDirectory = D.createDirectory
  getModificationTime = D.getModificationTime
  doesFileExist = D.doesFileExist
  doesDirectoryExist = D.doesDirectoryExist . dropFinalSlash
  getDirectoryContents = D.getDirectoryContents
  removeFile = D.removeFile

-- Quick workaround for a Cygwin problem:
dropFinalSlash = reverse . dropit . reverse
  where dropit ('/':s) = s
	dropit s = s

-- Inductive case:
instance (MT t,Functor (t m),Monad (t m),DirectoryIO m)
      => DirectoryIO (t m) where
  createDirectory      = lift . createDirectory
  getModificationTime  = lift . getModificationTime
  doesFileExist        = lift . doesFileExist
  doesDirectoryExist   = lift . doesDirectoryExist
  getDirectoryContents = lift . getDirectoryContents
  removeFile           = lift . removeFile

{-+
Time functions
----------------------
Operations corresponding to the standard library module #Time#.
(Only the subset requiring IO.)
-}

class (Functor m,Monad m) => TimeIO m where
  getClockTime :: m ClockTime
  toCalendarTime :: ClockTime -> m CalendarTime

instance TimeIO IO where
  getClockTime = Time.getClockTime
  toCalendarTime = Time.toCalendarTime

instance (MT t,Functor (t m),Monad (t m),TimeIO m) => TimeIO (t m) where
  getClockTime = lift getClockTime
  toCalendarTime = lift . toCalendarTime


{-+
Catching errors
---------------

This is the only class that lacks a general instance for monad transformers.
(It is probably a good idea to try to survive without relying on error
handlers...)
-}

class (Functor io,Monad io) => CatchIO ioerror io | io->ioerror where
  catch :: io a -> (ioerror -> io a) -> io a
  ioError :: ioerror -> io a

try m = fmap Right m `catch` (return . Left)
maybeM m = (Just `fmap` m) `catch` const (return Nothing)

bracket before after m =
  do x <- before
     r <- try (m x)
     after x
     returnTry r

bracket_ before after m =
  do x <- before
     r <- try m
     after x
     returnTry r

tryThen m after =
  do r <- try m
     after
     returnTry r

returnTry r = either ioError return r

instance CatchIO IOError IO where
  catch = Prelude.catch
  ioError = Prelude.ioError

--instance (MT t,Functor (t m),Monad (t m),CatchIO m) => CatchIO (t m) where
  -- !! How do you lift operations with negative occurences of m?

class IOErr ioerror where
  userError :: String -> ioerror
  isDoesNotExistError,isUserError :: ioerror -> Bool
  ioeGetErrorString :: ioerror -> String
  -- ..., ioeGetFileName, ...

instance IOErr IOError where
  userError = IO.userError
  isDoesNotExistError = IO.isDoesNotExistError
  isUserError = IO.isUserError
  ioeGetErrorString = IO.ioeGetErrorString
