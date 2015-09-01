module PfeSocket(listenOnPFE,connectToPFE,acceptPFE,removePFE,
                 pfeClient,clientOps,serverOps,sResult,errorString) where
import Prelude hiding (putStr,readIO)
import Network(listenOn,accept,connectTo,PortID(..))
import IO(hPutStrLn,hPrint,hGetLine,hGetContents,hClose,hSetBuffering,BufferMode(..))
import AbstractIO
import MUtils(ifM,done)
import SIO

listenOnPFE dir = ifM (doesFileExist (pfePath dir)) tryConnect listen
  where
    listen = listenOn (pfePort dir)

    tryConnect =
      do r <- try connect
         case r of
           Left _ -> cleanUp>>listen
	   Right _ -> backoff

    connect = do h <- connectToPFE dir
		 hPutStrLn h ""
		 s <- hGetContents h
		 seq (length s) done -- to avoid crashing the server
                 hClose h

    backoff = fail "PFE Server is already running"

    cleanUp = removePFE dir

acceptPFE s = do a@(h,_,_) <- accept s
		 hSetBuffering h IO.LineBuffering
		 return a

connectToPFE dir =
  do h <- connectTo "localhost" (pfePort dir)
     hSetBuffering h LineBuffering
     return h

pfeClient h args =
  do inBase $ hPutStrLn h (unwords args)
     clientLoop
     inBase $ hClose h
  where
    clientLoop =
       do msg <- inBase $ hReadLn h
	  case msg of
	    Stdout s -> putStr s >> clientLoop
	    Stderr s -> ePutStr s >> clientLoop
	    Result r -> case r of
			  Left s -> fail s
			  Right () -> done
			   

removePFE = removeFile . pfePath

pfePort = UnixSocket . pfePath
pfePath dir = dir++"/pfeserver"

data Msg = Stdout String | Stderr String | Result Result deriving (Read,Show)
type Result = Either String ()

serverOps h = StdIO {put=sPut h, eput=sePut h}
clientOps   = StdIO {put=putStr, eput=ePutStr {-. color-}}
--  where color s = "\ESC[31m"++s++"\ESC[m"

sPut h = hPrint h . Stdout
sePut h = hPrint h . Stderr
sResult h = hPrint h . Result . either (Left . show) Right

hReadLn h = readIO =<< hGetLine h

-- Work around the ugly way GHC prints user errors...
errorString e =
    if isUserError e
    then dropPrefix "user error\nReason: " (ioeGetErrorString e)
    else show e

dropPrefix (x:xs) (y:ys) | x==y = dropPrefix xs ys
dropPrefix _ ys = ys
