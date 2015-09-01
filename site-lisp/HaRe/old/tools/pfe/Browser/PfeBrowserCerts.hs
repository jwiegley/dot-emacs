module PfeBrowserCerts where
import Prelude hiding (putStr,putStrLn,print,readFile,ioError,catch,readIO)
import AllFudgets as Fud hiding (getModificationTime)
import FudDraw
import Maybe(isJust,listToMaybe,mapMaybe)
import MUtils
import AbstractIO
import FileUtils(readFileNow)
import DirUtils(latestModTime)
import List((\\))

import PfePlumbing
import PfeBrowserMonad
import PPU(pp{-,ppi,ppu,withPPEnv,($$),(<>),(<+>),PPHsMode-})
import PFE0
import PFE_Certs
import CertCmd
import CertServers(certFiles,lookupServer)
import PfePropCmds(tassertionSignature)
import CertAttrs(label)
import DrawLex(cstatusIcon,certIcon)
import QualNames(getQualified)
import TypedIds
import HsIdent(HsIdentI(..))
import TiNames(topName)

{-+ #evidenceGfx#: this function computes the table that is shown in the
Evidence window. Every existing certificate, certificate annotation and
assertion will be mentioned in one of the table entries.
-}
evidenceGfx m dir (bad,icons) certs asserts =
    htableD hdrs (concatMap certD certs++concatMap missingD missing)
  where
    hdrs = ["Icon","Name","Sequent (or other info)"]
    missing = [a|(a,_)<-asserts,pp a `notElem` concs]
    concs = mapMaybe (lookup "conc" @@ fst.snd) certs

    missingD a = [g bad,createCertD "" s,"?" |- HsCon a]
      where s = pp a

    certD (cert,(optattrs,status)) =
      case optattrs of
	Nothing -> [g bad,certNameD cert,
		    g "certificate does not exist (not created yet?)"]
	Just attrs ->
	  case (`lookup` icons) =<< lookup "type" attrs of
	    Just cicons ->
		[certIconD cert icon,certNameD cert, hyp |- a]
	      where
		icon = cstatusIcon cicons status
	    _ -> [g bad,certNameD cert,g "bad cert/unknown cert type"]
	  where
	    conc = fromMaybe "-" (lookup "conc" attrs)
	    hyp = fromMaybe "" (lookup "hyp" attrs)
	    --sequent = conc++" -| "++hyp
	    a = HsCon (topName Nothing m conc Assertion)

    certIconD cert icon = labelD (CertLbl cert) (g icon)

    hyp |- conc = hboxcD [g hyp,g "|-", assertionD conc]

    assertionD a = labelD (DefLbl a) (ulinkD (g (pp a)))

{-+ #getAssertionInfo#: compute the extra info that is shown when the user
clicks on an assertion name.
-}
getAssertionInfo (n,Assertion) =
  do allcs <- certs # getStBr
     cicons <- icons # getStBr
     let a = pp (getQualified n)
	 certs = [c|c@(_,(Just attrs,_))<-allcs,lookup "conc" attrs==Just a]
	 newc = head ((a:[a++show n|n<-[1..]])\\map fst allcs)
	 cis = [(cert,certIcon cicons cert)|cert<-certs]
     return [hboxcD' 10 (g "Certificates:":
			 (if null certs
			 then [g "none."]
			 else map certNameIconD cis)
			 ++[createCertD newc a])]
getAssertionInfo _ = return []


{-+ #visibleStatusChange#: calling #showCertInfo# or #showQCertInfo# can
cause the status of a certificate to be updated. This function returns true
when the status of a certificate in the current module changed, in which
case certificate icons should be redrawn and the internal state should be
updated.
-}
statusChange cert =
  do m <- modname # getStBr
     newstatus <- fmap fst # certStatus m cert
     oldstatus <- ((fmap fst . snd) # ) . lookup cert . certs # getStBr
     return $ Just newstatus/=oldstatus

{-+ #showCertInfo#: computes the certificate information displayed when the
user clicks on a certificate icon. This includes checking whether the
certificate is valid, invalid or outofdate.
-}
showCertInfo cert =
  do m <- modname # getStBr
     showQCertInfo (QCertName m cert)

showQCertInfo qcert =
    maybe idle inProgress . listToMaybe . certInProgress =<< getStBr
  where
    idle = showQCertInfo' qcert
    inProgress cmd =
      case cmdCert cmd of
        Just qcert' -> inProgress' cmd qcert'
	_ -> idle
    inProgress' cmd qcert' =
      if qcert'==qcert
      then popupCertInfo qcert $
	     spacedD centerS $
	     vboxD [g $ "Certificate server command in progress:",
		    g (shellCmd cmd)]
      else idle

showQCertInfo' qcert =
    do certinfo <- getCertDescription qcert
       pfePut (toRefs (linesD (briefTxt certinfo)))
       popupCertInfo qcert (fullGfx certinfo)
  where
    briefTxt (Left (msg,actionD)) = [g msg,actionD]
    briefTxt (Right (fields,_)) = map (g.join) (take 3 fields)
      where join (x,y) = x++": "++y

    fullGfx (Left (msg,actionD)) = vboxD [Fud.g msg,actionD]
    fullGfx (Right (fields,actionD)) =
	vboxD [htableD ["Field","Value"] flatfields,actionD]
      where flatfields = concatMap (\(x,y)->[g x,g y]) fields

    getCertDescription (QCertName m cert) =
      withWaitCursor $ 
      do let msg =g ("Checking status of certificate "++cert)
         putInfoWindow (CertInfo,msg)
	 pfePut (toRefs msg)
         dir <- checkProject
	 servers <- certServers # getStBr
	 (revalidate,status,info) <- certUpdStatus dir m =<< certInfo m cert
	 --let status = "Unknown"
	 optlogfile <- do let logfile = certDiagnosticsPath m cert dir
			  r <- try (readFileNow logfile)
			  return $ case r of
			             Right txt@(_:_) -> Just txt
			             _ -> Nothing

         return (certDescription (m,revalidate,optlogfile,status,servers) info)

    certDescription _ (cert,(Nothing,_)) =
        Left (cert++": certificate does not exist (not created yet?)", actionD)
      where
        actionD = createCertD cert ""

    certDescription (m,revalidate,optlogfile,status',servers)
                    (cert,(Just attrs,status)) =
      Right ([("Certificate",(cert++" :: "++ctype)),
              ("Current Status",status')]
--	     ++ cfield "Certifies" "conc"
--	     ++ cfield "Depends on" "hyp"
	     ++ showStatus status
	     ++ concat [cfield (label attrs) name|(name,attrs)<-cattrs]
	     ++ cfield "Created by" "who"
	     ++ sfield "About this certificate type" "description",
	     actionD)
      where
	showStatus Nothing = cfield "Date" "date"
	showStatus (Just (valid,when)) =
          [("Marked "++(if valid then "" else "in")++"valid on",show when)]

        ctype = fromMaybe "missing!!" (lookup "type" attrs)
	optserver = lookupServer servers ctype
	sattrs = maybe [] serverAttrs optserver
	cattrs = maybe [] certAttrs optserver
        cfield = field attrs
	sfield = field sattrs
        field attrs hdr name = maybe [] ((:[]).((,) hdr)) (lookup name attrs)

        actionD = hboxD' 20 (revalD++editD++logfileD++removeD)
          where
	    revalD  = if revalidate then [cmdD reval "Validate"] else []
	    removeD = [cmdD rm "Remove"]
	    logfileD = maybe [] logfile optlogfile
	      where
                logfile txt= [cmdD' (CertShowText txt) "View diagnostic output"]
	    editD =
	      if isJust optserver
	      then [cmdD' (CertEdit (ctype,(cert,attrs))) "Edit"]
	      else []

            cmdD  = cmdD' . CertCmd
            cmdD' cmd lbl = labelD cmd (ulinkD (g lbl))

            reval = ValidateCert mcert
	    rm    = RemoveCert mcert
	    mcert = QCertName m cert

    --showType = pfePut . toRefs @@ getType

revalidateAll =
    withWaitCursor $
    do dir <- checkProject
       m <- modname # getStBr
       mapM_ (certUpdStatus dir m @@ certInfo m . fst) . certs =<< getStBr

certUpdStatus dir m info@(cert,(a@(Just attrs),Just (valid,when))) =
    ifM auxchange (revalidate "auxiliary file changed/missing") $
    ifM srcchange
	(if valid
	 then certStatusFromSig
	 else revalidate "was invalid, some source file has been changed") $
    return (not valid,if valid then "Valid" else "Invalid",info)
  where
    auxchange = let auxfiles = certAuxFiles m cert attrs dir
		in anyChangeSince when auxfiles
    srcchange = do srcfiles <- map fst # getSubGraph (Just [m])
		   anyChangeSince when srcfiles -- not cached??

    revalidate why = return (True,"Needs revalidation ("++why++")",info)

    isUnconditionalCert =
      case (lookup "conc" attrs,lookup "hyp" attrs) of
	(Just conc,Just "..") -> Just conc
	_ -> lookup "test" attrs -- TestCase

    certStatusFromSig =
	maybe unknownStatus uncondCertStatusFromSig isUnconditionalCert

    unknownStatus = return (True,"unknown",info)

    uncondCertStatusFromSig conc =
      do optcertsig <-
	   maybeM (readIO =<< readFile (certDir m cert dir++"/deps"))
	 case optcertsig of
	   Nothing -> return (True,"New, not yet validated",info)
	   Just certsig ->
	     do srcsig <- tassertionSignature ((m,conc),Nothing)
		if certsig==srcsig
		  then do markValid m cert
			  st <- certStatus m cert
			  return (False,"Valid",(cert,(a,st)))
		  else revalidate "source changed"

    -- vaid/invalid status missing:
certUpdStatus _ _ info@(_,(Just _,_)) =
    return (True,"New, not yet validated",info)

    -- attributes missing:
certUpdStatus _ _ info = return (False,"unknown (attributes missing?!)",info)

quickCertsStatus m certs dir =
  do srcdate <- latestModTime . map fst =<< getSubGraph (Just [m])
     mapM (quickCertStatus m srcdate dir) certs

quickCertStatus m srcdate dir cert =
  do (optattrs,status) <- snd # certInfo m cert
     case (,) # optattrs <# status of
       Nothing -> return Nothing
       Just (attrs,status@(valid,when)) ->
	 if srcdate>when
	 then return Nothing
	 else ifM (anyChangeSince when (certAuxFiles m cert attrs dir))
		  (return Nothing)
		  (return (Just status))

--allCertFiles m cert dir = (++) # certAuxFiles m cert dir <# certSrcFiles m
certAuxFiles m cert attrs dir = certAttrsPath m cert dir:certFiles attrs
--certSrcFiles m = map fst # getSubGraph [m]

createCertD cert concl = labelD (CreateCert (cert,concl))
			        (ulinkD (g "Create a new certificate!"))

certNameD cert = labelD (CertLbl cert) (ulinkD (g cert))

certNameIconD ((c,_),icon) = labelD (CertLbl c) (hboxD [ulinkD (g c),g icon])

htableD hdrs cells = tableD' 0 (length hdrs) (map b hdrs++map f cells)
  where
    b x = stackD [fgD "grey" (g $ filler False False 5),padD 3 (g x)]
    f x = stackD [fgD "grey" (g frame),padD 3 x]
    --f x = padD 3 x

linesD = fontD defaultFont . vboxlD' 0 -- . map g

anyChangeSince when paths =
   ifM (allM doesFileExist paths)
       ((when<) # latestModTime paths)
       (return True) -- a file has been deleted
