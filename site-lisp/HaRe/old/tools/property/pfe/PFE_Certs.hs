module PFE_Certs(module PFE_Certs,CertServers,CertServer(..)) where
import Prelude hiding (putStrLn,ioError,catch,writeFile)
import Maybe(fromMaybe)

import HsModule
import HasPropStruct
import HsPropStruct(PD(..))
import PFE0(projectDir,moduleInfoPath,getSubGraph)
import CertServers

import AbstractIO
import DirUtils(getModificationTimeMaybe)
import MUtils

type CertType = String
type CertName = String
data QCertName = QCertName ModuleName CertName deriving (Eq,Show,Read)

-- Extract the named assertions from the top-level of a module:
assertions mod =
  [(n,pa)|Just (HsAssertion s (Just n) pa)<-map propstruct (hsModDecls mod)]

getCertServers = getCertServers' =<< getProgramaticaDir

getCertServers' = readCertServers . certTypesDir

getProgramaticaDir =
  do pdir <- fromMaybe defaultPDir # maybeM (getEnv pDirVar)
     unlessM (doesDirectoryExist pdir) $
       fail $ "Didn't find the Programatica directory "++pdir
     let pdir' = if take 1 (reverse pdir) == "/" then pdir else pdir++"/"
     return pdir'

type CertStatus = Maybe (Bool,ClockTime) -- (valid?,when)
--certStatus :: ... => Module -> CertName -> m CertStatus
certStatus m cert =
    do optdir <- projectDir
       case optdir of
         Nothing -> return Nothing
	 Just dir ->
	   status # getModificationTimeMaybe (certValidWhenPath m cert dir)
		 <# getModificationTimeMaybe (certInvalidWhenPath m cert dir)
  where
    status optvalid optinvalid =
      case (optvalid,optinvalid) of
	(Just v,Just inv) -> if v>inv then Just (True,v) else Just (False,inv)
	(Just v,_) -> Just (True,v)
	(_,Just inv) -> Just (False,inv)
	_ -> Nothing

type CertInfo = (CertName,(Maybe Attrs,CertStatus))

--certInfo :: ... => Module -> CertName -> CertInfo
certInfo m cert =
  do optdir <- projectDir
     (,) cert # case optdir of
	         Nothing -> return (Nothing,Nothing)
                 Just dir -> (,) # certAttrs dir <# certStatus m cert
  where
    certAttrs dir = maybeM (readAttrs path)
      where path = certAttrsPath m cert dir

markValid m cert =
  do optdir <- projectDir
     case optdir of
       Just dir -> do now <- getClockTime
                      writeFile (certValidWhenPath m cert dir) (show now)
		      srcfiles <- map fst # getSubGraph (Just [m])
		      writeFile (certSrcListPath m cert dir) (unlines srcfiles)
       _ -> done

--optCertsDir = certsDir # projectDir

--------------------------------------------------------------------------------

certsDir dir = dir++"cert/" -- or just "cert/", or "evidence/"? (dir="hi")
certModuleDir m dir = certsDir dir++moduleInfoPath m
certDir m f dir = certModuleDir m dir++"/"++f
--certIconPath m f = certDir m f++"/icon.gif"
certAttrsPath m f dir = certDir m f dir++"/cert.attr"
--certTextPath m f dir = certDir m f dir++"/cert.txt"
certDiagnosticsPath m f dir = certDir m f dir++"/output.txt"
badCertIconPath pdir = pdir++"icons/smiley.sad.gif"
--certDatestampPath m = certDir m "when"
certValidWhenPath m c dir = certDir m c dir++"/valid"
certInvalidWhenPath m c dir = certDir m c dir++"/invalid"
certSrcListPath m c dir = certDir m c dir++"/srclist.txt"
-- Programatica directory:
pDirVar = "PROGRAMATICA"
certTypesDir pdir = pdir++"types/certificate/"

-- Suitable builtin default for the PacSoft servers:
defaultPDir = "/home/projects/pacsoft/tools/lib/Programatica/"
