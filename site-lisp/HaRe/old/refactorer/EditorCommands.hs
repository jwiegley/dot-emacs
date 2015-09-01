module EditorCommands where

import MT(MT(..))

import System.Cmd(system)
import System.Environment(getArgs)
import System.IO(hPutStrLn
         ,hGetLine
         ,hClose
         ,hSetBuffering
         ,BufferMode(..)
         ,IOMode(..)
         ,Handle
         ,stdin
         ,stderr)
import Control.OldException as Exception
import Foreign
import Foreign.C
import Network hiding (listenOn,connectTo,accept)
import Network.BSD(getProtocolNumber
                  ,getHostByName
                  ,getHostByAddr
                  ,hostAddress
                  ,HostEntry(..))
import Network.Socket(Family(..)
                     ,SocketType(..)
                     ,SockAddr(..)
                     ,SocketOption(..)
                     ,socket
                     ,sClose
                     ,setSocketOption
                     ,bindSocket
                     ,listen
                     ,connect
                     ,socketToHandle
                     ,iNADDR_ANY
                     ,maxListenQueue
                     ,inet_ntoa
                     ,recv
                     ,send
                     )
import qualified Network.Socket as Socket(accept)

data EditorCmds = EditorCmds 
  { getEditorCmd :: IO String                   
  , sendEditorMsg :: Bool -> String -> IO () -- False: just log, 
                                             -- True: make visible
  , sendEditorModified :: String -> IO ()
  }

-- default, useful for testing
commandlineCmds =
  EditorCmds{getEditorCmd={- hSetBuffering stdin LineBuffering >> -} getLine
            ,sendEditorModified= \f->hPutStrLn stderr $ "modified: "++f
            ,sendEditorMsg= \d m-> if d then hPutStrLn stderr $ "message: "++m 
                                        else hPutStrLn stderr m}

-- refactorer is asynchronous subprocess of emacs,
-- which controls refactorers stdin and stdout;
-- seems to be relatively portable; emacs side will
-- need to interpret backchannel as editor-commands 
emacsCmds = 
  EditorCmds{getEditorCmd=getLine
            ,sendEditorModified= \f->hPutStrLn stderr $ "modified: "++f
            ,sendEditorMsg= \d m-> if d then hPutStrLn stderr $ "message: "++m 
                                        else hPutStrLn stderr m}

-- refactorer is independent process started from vim;
-- we listen on socket for commands from vim (via refactoring
-- client), and answer with direct editor-commands, using 
-- vim's clientserver functionality
mkVimCmds vimPath vimServerName = lift $ withSocketsDo $ do
  s <- listenOn $ PortNumber 9000
  return EditorCmds{
    getEditorCmd=getInput s
   ,sendEditorModified= \f-> do 
      let cmd = vim_remote $
                  "call Haskell_refac_modified("++squote f++")"
      hPutStrLn stderr cmd
      system cmd  
      return ()
   ,sendEditorMsg= \b s-> do 
      let dialog = if b then "1" else "0"
          cmd = vim_remote $
                  "call Haskell_refac_msg("++dialog++","++dquote s++")"
      hPutStrLn stderr cmd
      system cmd  
      return ()
   }
  where
    -- which vim to call?? the caller will tell us,
    -- but in case it's a gvim, we need to avoid pop-up dialogs
    vim_remote cmd = vimPath++" --servername "++vimServerName
                            ++" --remote-send \":silent "++cmd++" | silent redraw <cr>\""
    squote s           = "'"++concatMap del_quotes s++"'" -- no quotes or special chars in single quotes..:-((
    dquote s           = "'"++concatMap del_quotes s++"'" -- vim remote in win98 reads any " as comment start:-(
    del_quotes c | c `elem` "'\"" = " "
		 | c == '\n'	  = "\\n"
		 | otherwise      = [c]
    getInput s = do
      (h,host,portnr) <- accept s
      hSetBuffering h LineBuffering
      l <- hGetLine h
      hPutStrLn h "<ack>"
      putStrLn $ "SERVER: '"++l++"'"
      -- hClose h
      return l

clientCmd :: IO ()
clientCmd = withSocketsDo $ do
  args <- getArgs
  h <- connectTo "localhost" $ PortNumber 9000
  hSetBuffering h LineBuffering
  hPutStrLn stderr $ "(stderr) CLIENT SEND: "++unwords args
  putStrLn $ "(stdout) CLIENT SEND: "++unwords args
  hPutStrLn h $ unwords args
  hGetLine h  -- wait for acknowledgement
  return ()


-- | Creates the server side socket which has been bound to the
-- specified port.  
--
-- NOTE: To avoid the \"Address already in use\"
-- problems popped up several times on the GHC-Users mailing list we
-- set the 'ReuseAddr' socket option on the listening socket.  If you
-- don't want this behaviour, please use the lower level
-- 'Network.Socket.listen' instead.

{-
foreign import stdcall unsafe "WSAGetLastError"
  c_getLastError :: IO CInt

foreign import ccall unsafe "getWSErrorDescr"
  c_getWSError :: CInt -> IO (Ptr CChar)
-}

listenOn :: PortID 	-- ^ Port Identifier
	 -> IO Socket	-- ^ Connected Socket

listenOn (PortNumber port) = do
--    proto <- getProtocolNumber "tcp"
--    putStrLn $ "tcp: "++show proto
    let proto = 6 -- bug in ghc's getProtocolNumber..
    EditorCommands.bracketOnError
      (Exception.catch (socket AF_INET Stream proto)
          (\e-> do
--          errCode <- c_getLastError
            -- perr <- c_getWSError errCode
            -- err <- peekCString perr
--          putStrLn $ "WSAGetLastError: "++show errCode
            throw e))

	(sClose)
	(\sock -> do
	    setSocketOption sock ReuseAddr 1
	    bindSocket sock (SockAddrInet port iNADDR_ANY)
	    listen sock maxListenQueue
	    return sock
	)

bracketOnError
	:: IO a		-- ^ computation to run first (\"acquire resource\")
	-> (a -> IO b)  -- ^ computation to run last (\"release resource\")
	-> (a -> IO c)	-- ^ computation to run in-between
	-> IO c		-- returns the value from the in-between computation
bracketOnError before after thing =
  block (do
    a <- before 
    r <- Exception.catch 
	   (unblock (thing a))
	   (\e -> do { after a; throw e })
    return r
 )

-- | Calling 'connectTo' creates a client side socket which is
-- connected to the given host and port.  The Protocol and socket type is
-- derived from the given port identifier.  If a port number is given
-- then the result is always an internet family 'Stream' socket. 

connectTo :: HostName		-- Hostname
	  -> PortID 		-- Port Identifier
	  -> IO Handle		-- Connected Socket

connectTo hostname (PortNumber port) = do
--    proto <- getProtocolNumber "tcp"
--    putStrLn $ "tcp: "++show proto
    let proto = 6 -- bug in ghc's getProtocolNumber..
    EditorCommands.bracketOnError
	(Exception.catch (socket AF_INET Stream proto)
          (\e-> do
--          errCode <- c_getLastError
--          putStrLn $ "WSAGetLastError: "++show errCode
            throw e))
	(sClose)  -- only done if there's an error
        (\sock -> do
      	  he <- getHostByName hostname
      	  connect sock (SockAddrInet port (hostAddress he))
      	  socketToHandle sock ReadWriteMode
	)

-- -----------------------------------------------------------------------------
-- accept

-- | Accept a connection on a socket created by 'listenOn'.  Normal
-- I\/O opertaions (see "System.IO") can be used on the 'Handle'
-- returned to communicate with the client.
-- Notice that although you can pass any Socket to Network.accept, only
-- sockets of either AF_UNIX or AF_INET will work (this shouldn't be a problem,
-- though). When using AF_UNIX, HostName will be set to the path of the socket
-- and PortNumber to -1.
--
accept :: Socket 		-- ^ Listening Socket
       -> IO (Handle,  -- Socket, -- should be: Handle,
	      HostName,
	      PortNumber)	-- ^ Triple of: read\/write 'Handle' for 
				-- communicating with the client,
			 	-- the 'HostName' of the peer socket, and
				-- the 'PortNumber' of the remote connection.
accept sock {- @(MkSocket _ AF_INET _ _ _) -} = do
 ~(sock', (SockAddrInet port haddr)) <- Socket.accept sock
 peer <- Exception.catchJust ioErrors
	  (do 	
	     (HostEntry peer _ _ _) <- getHostByAddr AF_INET haddr
	     return peer
	  )
	  (\e -> inet_ntoa haddr)
		-- if getHostByName fails, we fall back to the IP address
 -- return (sock', peer, port)
 handle <- socketToHandle sock' ReadWriteMode
 return (handle, peer, port)

