module CertServers(
   CertServer(..),CertServers,readCertServers,
   Attr,Attrs,Name,readAttrs,parseAttrs,printAttrs,certFiles,lookupServer
 ) where

import Prelude hiding (readFile)
import AbstractIO
import Maybe(catMaybes,mapMaybe,listToMaybe)
import List(partition)
import MUtils

import Attrs
import ParseAttrs
import ParseCertAttrs

data CertServer = Server {serverName :: Name,
			  serverDir :: FilePath,
			  serverAttrs :: Attrs,
			  certAttrs :: CertAttrs }
		deriving Show

type CertServers = [CertServer]

--readCertServers :: FilePath -> IO CertServer
readCertServers certServerDir =
  collectWith (readServer certServerDir) =<< getDirectoryContents certServerDir

--readServer :: String -> String -> IO CertServer
readServer certServerDir name
 = do let serverRoot = certServerDir++name
          serverAttr = serverRoot `fileSep` "server.attr"
	  splitAttrs = partition ((=="attribute").fst)
      (certattrs,servattrs) <- splitAttrs # readAttrs serverAttr
      return Server{serverName = name,
		    serverDir = serverRoot,
		    serverAttrs = servattrs,
		    certAttrs = mapMaybe parseCertAttr (map snd certattrs)}
				-- Hmm. Errors are silently ignored!!

--collect       :: (a->IO b) -> [a] -> IO [b]
collectWith m xs = catMaybes # mapM (maybeM . m) xs

fileSep :: FilePath->FilePath->FilePath
fileSep dir file = dir ++ "/" ++ file

lookupServer :: CertServers -> Name -> Maybe CertServer
lookupServer servers ctype = listToMaybe [s|s<-servers,serverName s==ctype]
