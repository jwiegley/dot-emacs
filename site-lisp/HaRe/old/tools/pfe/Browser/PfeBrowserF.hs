module PfeBrowserF(mainF) where
import Prelude hiding (putStr,putStrLn,print,readFile,writeFile,ioError,catch,readIO)
import Monad(unless,mplus,when,filterM)
import Maybe(fromMaybe,mapMaybe,isJust)
import List(find,(\\),nub)
import AllFudgets as Fud hiding (getModificationTime)
import ContribFudgets hiding (lift)

import FudgetIOMonad1
import PfePlumbing
import PfeBrowserMonad
import IdInfo
import PfeBrowserGUI
import CertAttrsEditorF
import PfeBrowserMenu as M
import PfeBrowserCerts
import CertServerF
import CertCmd
import AuxWindowsF
import ImageGraphics(gifFile)
import FudExtras(longTextPopupF)

import HsModule(ModuleName(..),hsModName,{-,HsModuleI-})
import HsTokens as T
import PropPosSyntax(getHSName,SrcLoc(..))
import TiDecorate(no_use)
import TI(Typing(..),envFrom,topName,HsIdentI(..))
import PNT(PNT(..))
import TypedIds(namespace,isClassOrType)
import UniqueNames as UN(OptSrcLoc(N),optOrigModule)
import HasBaseName(getBaseName)

import PFE0(getModuleInfixes,setBatchMode,checkProject,ppFlags,
	    withProjectDir,epput,
	    updateModuleGraph,findNode,projectDir,getCurrentModuleGraph)
import PFE2(getModuleExports)
import PFE3(parseSourceFile'')
import ScopeModule(checkRefs)
import PFE4(exTypeCheck)
import Pfe2Cmds(ppExports)
import Pfe4Cmds(ppIface,moduleInterface)
import PFE_Certs
import CertServers(printAttrs)

import PPU(pp,ppi,ppu,withPPEnv,($$),(<>),(<+>),vcat)
import DrawDoc(drawDoc)
import DrawError
import DrawLex(origLabel,certIcon)
import FudDraw(ulinkD)
import MT(lift)
import MUtils
import AbstractIO hiding (getEnv)
import FileUtils(updateFile)
import SimpleGraphs(reverseGraph,neighbours)
import StatusIndicator(statusF,Status(..))

-- Debuging
--import IOExts(trace)

--- Plumbing -------------------------------------------------------------------

mainF opts pdir servers =
    loopOnlyF $ titleShellF' (setSizing Static) myversion pfeBrowserF
  where
    pfeBrowserF = pfeF opts >==< guiF

    -- @ guiF : the graphical user interface fudget of the PFE browser
    guiF :: F Out In
    TagF guiF dispatch tags =
	mapTF vBoxF $
	    (mapTF hBoxF (pfeMenuBarTF>&<statusTF) >&< infoWindowsTF)
	>&< compTagF (hSplitF' aLeft) graphDispTF moduleDispTF
	>&< (popupsTF >&< certServerTF)

    toTitle = Left
    (_toMenuBar:&:toStatus:&:_toInfoWindows):&:(toGraph:&:toModuleDisp)
     :&:(toPopups:&:toCertServer)=
	extend Right tags
    toMessagePopup:&:toNewCertPopup:&:(toCertAttrsEditors:&:toTextEditor) = toPopups

    pfeMenuBarTF = tagF fromMenuBar (pfeMenuBarF types)
      where
        types = [serverName s|s<-servers,
		              lookup "has_sequent" (serverAttrs s)/=Just "no"]

    statusTF = tagF (const done)
                    (spacer1F centerS $ {-"Status:" `labLeftOfF`-} statusF)

    popupsTF = messagePopupTF >&< newCertPopupTF >&<
	       (certAttrsEditorsTF >&< textEditorPopupTF)
      where
	messagePopupTF = tagF fromMessagePopup (snd>^=<longTextPopupF)
	newCertPopupTF = tagF fromNewCertPopup newCertPopupF
	certAttrsEditorsTF = tagF fromCertAttrsEditor dynCertAttrsEditorPopupsF
	textEditorPopupTF = tagF fromTextEditor textEditorPopupF

    graphDispTF = tagF fromGraph graphDispF
    certServerTF = tagF fromCertServer certServerF -- actually not a GUI part...

    toNodeInfo:&:(_toSource:&:_toRefs) = toModuleDisp
    moduleDispTF =
	mapTF vBoxF $     tagF fromNodeInfo nodeInfoF
		      >&< compTagF (vSplitF' aBottom)
				   (tagF fromSource sourceDispF)
				   (tagF fromRefs refDispF)

    infoWindowsTF = tagF fromInfoWindows $
		    spacer1F (noStretchS False True `compS` rightS) $
		    auxGfxWindowsF myname

    fromGraph = newNode
    fromNodeInfo = either newModuleLbl newFile
    fromRefs = infoPick Nothing
    fromMessagePopup _ = done

    fromInfoWindows = either popupInfoWindow infoPick'
      where infoPick' (w,infolbl) = infoPick (Just w) infolbl

    infoPick optw infolbl =
      case infolbl of
	CertLbl cert -> clearRefs >> changeHilite [] >> updCertInfo cert
        DefLbl (HsCon (PNT pn sp _)) -> goto (HsCon pn,sp)
        DefLbl (HsVar (PNT pn sp _)) -> goto (HsVar pn,sp)
	SrcLocLbl (path,pos) -> newFile path >> gotoLabel (posLabel pos)
          where gotoLabel lbl = do pfePut . toSource . mkvis $ lbl
			           changeHilite [lbl]
        ModuleLbl m -> newModuleLbl (m,Nothing)
	CertCmd cmd@(ValidateCert qcert) ->
	    do putCertServer cmd
	       vcert <- certDisplay # getStBr
	       when (vcert==Just qcert) $ showQCertInfo qcert
	CertCmd cmd ->
	    do maybe done close optw
	       putCertServer cmd
	  where
	    close w = popupInfoWindow (w,False)

	CreateCert ca -> newCertPopup ca
	CertEdit e -> pfePut (toCertAttrsEditors (Right e))
	CertShowText txt -> pfePut . toMessagePopup . map backspace . lines $ txt
	ShowErrorMsg gfx -> popupErrorMsg gfx

    newCertPopup ca =
      do cicons <- certIcons # getStBr
	 clearRefs
	 pfePut (toNewCertPopup (cicons,ca))

    putCertServer cmd =
	do cmds <- certInProgress # getStBr
	   setInProgress (cmds++[cmd])
	   if null cmds then doCertServer shellcmd else notnow
      where
	shellcmd = shellCmd cmd
	notnow = certCmdMsg "Command added to queue" shellcmd

    -- pre: no command in progress
    doCertServer shellcmd =
	do certCmdMsg "Sent certificate server command" shellcmd
	   pfePut (toCertServer shellcmd)

    certCmdMsg msg cmd =
      do cnt <- length . certInProgress # getStBr
         pfePut $ toRefs $ linesD $
		    [g $ msg++":", g cmd]
		    ++(if cnt>0
		       then [g $ "Number of commands in queue: "++show cnt]
		       else [])

    fromNewCertPopup (ty,(cert,concl)) =
      if null cert || null concl
      then popupMsg "Fill in both a certificate name and a conclusion when creating a new certificate!"
      else do m <- modname # getStBr
	      let qcert = QCertName m cert
		  cmd = CertCmd.NewCert ty qcert concl
	      putCertServer cmd
	      dcert <- certDisplay # getStBr
	      when (dcert==Just qcert) $ showQCertInfo qcert

    fromCertAttrsEditor (ctype,(cname,userattrs)) =
      do Just dir <- projectDir
	 m <- modname # getStBr
	 (_,(Just oldattrs,_)) <- certInfo m cname
	 let newattrs = updateAttrs oldattrs userattrs
	 updateFile (certAttrsPath m cname dir) (printAttrs newattrs)
	 infoPick Nothing (CertLbl cname) -- hmm
     where
	updateAttrs oldattrs newattrs =
	    map replace oldattrs++addedattrs -- preserve the order!
	  where
	    addedattrs = filter added newattrs
	    added (n,_) = n `notElem` map fst oldattrs
	    replace (name,old) = (name,fromMaybe old (lookup name newattrs))

    fromTextEditor ((_,Just src),src') =
	if src'/=src
	then do srcpath <- fst . modnode # getStBr
		-- This assumes that the editor window is modal, so that
		-- the current node still is the same!!
		writeFile srcpath src'
		reloadModule
	else done
    fromMenuBar msg = 
      case msg of
	File fcmd -> fileCmd fcmd
	View vcmd -> viewCmd vcmd
	Windows wcmd -> windowCmd wcmd
	Cert ccmd -> certCmd ccmd
	_ -> done -- !!
      where
	fileCmd Quit = pfeQuit
	fileCmd ReloadModule = reloadProject
	fileCmd EditModule = editModule

	viewCmd vcmd = do updStBr $ \ st->st{viewMode=vcmd}
			  optGetTypes

	windowCmd (WindowCmd w up) =
	    pfePut (toInfoWindows (w,Left up)) --up is False or True

	certCmd certcmd =
	  case certcmd of
	    M.NewCert -> whenInModuleM $ newCertPopup ("","")
	    M.NewAll certtype -> whenInModuleM $ newAll certtype
	    M.TodoCert -> putCertServer CertCmd.TodoCert
	    RevalidateAllQuick -> revalidateAll >> reloadModule
	    ValidateAll -> validateAll
	    _ -> done -- !!

        newAll ty =
          do m <- modname # getStBr
             putCertServer $ CertCmd.NewCertAll ty (pp m)

        validateAll =
          do m <- modname # getStBr
	     let qcert = QCertName m
		 validateOne = putCertServer . ValidateCert . qcert . fst
	     mapM_ validateOne. certs =<< getStBr

	editModule =
	   do n <- modnode # getStBr
	      unless (isNoModule n) $
		do let srcpath = fst n
		       mname = fst (snd n)
		       prompt = "Edit "++pp mname++" in "++srcpath
		   src <- readFile srcpath
		   pfePut (toTextEditor (Just prompt,Just src))

    fromCertServer (ok,output) =
      do cmds <- certInProgress # getStBr
	 let cmds' = drop 1 cmds
	 setInProgress cmds'
	 if null cmds'
	    then do clearRefs
		    changeHilite []
		    {-when ok-}
		    reloadModule
            else doCertServer (shellCmd (head cmds'))
	 unless (null output) (route cmds . map stripEither $ output)
      where
	route (ValidateCert qcert:_) msg =
	    certCmdMsg (ppqcert qcert) (last msg)
	route _ msg =
	  if ok && length msg <= 3
	  then pfePut . toRefs . linesD . map g $ msg
	  else pfePut $ toMessagePopup msg

    --- Initialization and main loop -------------------------------------------

    --pfeF o = nullF
    pfeF :: Opts -> PfeF
    pfeF = runFIOM . runPfeFM pfeFM

    pfeFM :: PfeFM ()
    pfeFM =
	do g <- getCurrentModuleGraph
	   icons <- getCertIcons servers
	   sadicon <- getIcon (gifFile (badCertIconPath pdir))
	   setStBr St{modnode=noModuleNode,viewMode=view0,mrefs=[], hilbls=[],
		     types=Nothing,certs=[],revgraph=reverseGraph (map snd g),
		     certDisplay=Nothing,certInProgress=[],
		     certServers=servers,certIcons=icons,sadIcon=sadicon}
	   pfePut (toGraph g)
	   putInfoWindow (CertTypes,drawCertTypes (zip servers icons))
	   pfePut (toCertAttrsEditors (Left servers))
	   setBatchMode False
	   pfeloop
      where	  
	pfeloop :: PfeFM ()
	pfeloop =
	  do (dispatch =<< pfeGet) `catch` stdHandler
	     pfeloop

	getCertIcons :: CertServers -> PfeFM CertIcons
	getCertIcons servers = mapM getCertIcon servers
	getCertIcon certServer =
	  do let dir = serverDir certServer
		 certtype = serverName certServer
		 iconsrc status = gifFile (dir++"/"++status++".gif")
	     valid   <- getIcon (iconsrc "valid")
	     invalid <- getIcon (iconsrc "invalid")
	     unknown <- getIcon (iconsrc "unknown")
	     return (certtype,(valid,invalid,unknown))

	getIcon = lift . xrequestFIOM . convToPixmapK

	drawCertTypes = htableD hdrs . concatMap certD
	  where
	    hdrs = ["Icon","Type","Description"]
	    certD (server,(ty,(icon,_,_))) = [g icon,g ty,g descr]
	      where
		descr = fromMaybe "(Descrption missing)" $
			lookup "description" (serverAttrs server)

    typeErrorHandler err =
      do --setNoTypes
	 pfePut $ toRefs $ fgD "red" $ g "Type error!"
	 setStatus (Typing,InError)
         --o <- ppFlags
	 m <- modname # getStBr
         popupErrorMsg (fontD ppfont (drawTypeError m err))
	 epput err
	 
{-
    setNoTypes = do updStBr $ \ st->st{viewMode=Hyper}
		    putStrLn "Switching off type info"
		    pfePut (toMenuBar (View Hyper))
-}
    stdHandler err =
	do epput msg
	   -- popupMsg msg
	   unless (null msg) $ popupErrorMsg (msgGfx msg)

      where msg = ioeGetErrorString err

    popupErrorMsg gfx =
	do putInfoWindow (ErrorMsg,gfx)
	   popupInfoWindow (ErrorMsg,True)

    clearErrorMsg = putInfoWindow (ErrorMsg,blankD 10)

    setStatus = pfePut . toStatus

    resetStatus = sequence_ [setStatus (l,Unknown)|l<-[minBound..maxBound]]

    whenInModuleM = unlessM (isNoModule.modnode # getStBr)


    --- Reactions and auxiliary functions --------------------------------------

    reloadProject =
	-- skip reload if there is no project, or no module is selected
	whenInModuleM $ reloadGraph >> reloadModule
      where
	reloadGraph =
	  do updateModuleGraph
	     -- should also check for added/removed files and update graphDispF
	     updModNode . modname =<< getStBr

    updModNode m =
      do g <- getCurrentModuleGraph
	 node <- findNode m
	 updStBr $ \st->st{revgraph=reverseGraph (map snd g),modnode=node}
	 return node

    reloadModule =
      whenInModuleM $
	do maybe done showQCertInfo . certDisplay =<< getStBr
	   newNode . modnode =<< getStBr

    {-+ #newNode#: load and display a new module, after the user has entered or
	 clicked on a module name or a file name. -}
    newNode node@(path,_) =
      withWaitCursor $
      do resetStatus
	 clearErrorMsg
	 setStatus (Syntax,InProgress)
         dir <- checkProject
	 --pfePut (toSource (Left ("","",[]))) -- empty window to scroll to top
	 r <- try (parseSourceFile'' path)
	 case r of
	   Left err -> badNode dir err
	   Right (ts,((wm,ast),refs)) ->
	    do node@(_,(m,_)) <- updModNode (getBaseName (hsModName ast)) --updates revgraph
	       let --refs =simplifyRefsTypes' rs
		   asserts = assertions ast -- :: [(PNT,AssertionI PNT)]
		   certs_annot = mapMaybe isCertToken ts -- :: [CertName]
		   isCert cert = doesFileExist (certAttrsPath m cert dir)
	       certs_existing <- filterM isCert . fromMaybe [] =<<
			    maybeM (getDirectoryContents (certModuleDir m dir))
	       let certs_noannot = certs_existing \\ certs_annot
		   certs = certs_annot++certs_noannot
	       certsStatus <- zip certs # quickCertsStatus m certs dir
	       certsInfo <-
		  let replace = zipWith replace1 certsStatus
		      replace1 (_,s) (c,(a,s0)) = (c,(a,s))
		  in replace # mapM (certInfo m) certs
	       let conccert (cert,(attrs,_)) =
                     flip (,) cert # (lookup "conc" =<< attrs)
                   na = collectByFst .
			mapMaybe conccert .
			filter ((`elem` certs_noannot).fst) $
			certsInfo
	       updStBr $ \st->st{mrefs=refs,hilbls=[],types=Nothing,certs=certsInfo}
	       e <- getModuleExports m
	       -- To keep the displays consistent with the internal state,
	       -- output operations should come after all operations that can fail!
	       setStatus (Syntax,Good)
	       setStatus (Scoping,InProgress)
	       scope_ok <- showScopeErrors refs
	       setStatus (Scoping,if scope_ok then Good else InError)
	       importedby <- flip neighbours m . revgraph # getStBr
	       pfePut (toNodeInfo (Left (node,importedby)))
	       cicons <- icons # getStBr
	       pfePut (toSource (Left (dir,cicons,node,ts,refs,certsStatus,na)))
	       o <- ppFlags
	       putInfoWindow (Exports,ppo o (ppExports m e))
	       putInfoWindow (Interface,ppMsgGfx o clickToActivate)
	       putInfoWindow (Pretty,ppo o ast)
	       putInfoWindow (Evidence,evidenceGfx m dir cicons certsInfo asserts)
	       pfePut (toTitle (myname++": "++pp m))
	       when scope_ok optGetTypes
      where
	{-+
	Rather than aborting newNode (and potentially leaving the history buttons
	in an incosistent state) on errors, display an empty window and continue...
	-}
	badNode dir err =
	  do o <- ppFlags
	     s <- fromMaybe [] # maybeM (readFile path)
	     updStBr $ \st->st{modnode=node}
	     pfePut (toRefs (ppMsgGfx o (ioeGetErrorString err)))
	     pfePut (toNodeInfo (Left (node,[])))
	     pfePut (toSource (showsrctext s))
	     setStatus (Syntax,InError)
	     putInfoWindow (Exports,blankD 10)
	     putInfoWindow (Interface,blankD 10)
	     putInfoWindow (Pretty,blankD 10)
	     putInfoWindow (Evidence,blankD 10)
	     pfePut (toTitle (myname++": "++path))

	showScopeErrors refs =
	    do if ok
		 then clearRefs
		 else do o <- ppFlags
			 pfePut (toRefs (gfx o))
	       return ok
	    where
              ok = null errs
	      errs = checkRefs refs
	      errcnt = length errs

	      gfx o =
                labelD (ShowErrorMsg (fontD ppfont (drawScopeErrors errs)))
		       (ulinkD (g msg))

	      msg = if errcnt==1
		    then "One scoping error"
		    else show errcnt++" scoping errors"

    {-+ #newModule#: load and display a new module after the user has entered
	or clicked on a module name. -}
    newModule :: ModuleName ->PfeFM ()
    newModule m = newNode =<< findNode m

    newModuleLbl (m',optlbl) =
      do n@(_,(m,_)) <- modnode # getStBr
	 when (isNoModule n || m'/=m) $ newModule m'
	 maybe done gotoLabel optlbl
      where
	gotoLabel lbl = do pfePut . toSource . mkvis $ lbl
			   showInfo lbl

    {-+ #newFile#: load and display a new module after the user has entered or 
	clicked on a file name. -}
    newFile :: FilePath ->PfeFM ()
    newFile path =
      do (oldpath,_) <- modnode # getStBr
	 when (path/=oldpath) $
	   do updateModuleGraph
	      g <- getCurrentModuleGraph
	      case [node|node@(path',_)<-g,path'==path] of
		[node] -> newNode node
		_ -> fail ("File not part of this project:"++path)

    {-
    goto o@(_,r) =
      case r of 
	Left (s,n) ->
	  do let m' = Module s
	     m <- modname # getStBr
	     unless (m'==m) $ newModule m'
	     gotoLocal o
	_ -> gotoLocal o
    -}

    goto o@(r,_) =
	  do let optm' = optOrigModule r
	     m <- modname # getStBr
	     case optm' of
	       Just m'| m'/=m -> newModule m'
	       _ -> done
	     gotoLocal o

    gotoLocal (o,sp) =
      do st <- getStBr
	 case [r|r@((d,_),_,[(o',sp')])<-mrefs st,
		 isDef d,o'==o,namespace sp'==namespace sp]
	   of orig:_ -> do let lbl = origLabel orig
			   pfePut (toSource (mkvis lbl))
			   rememberLbl lbl
			   showInfo lbl
	      _ -> putStrLn $ "Didn't find def of "++show o

    rememberLbl lbl = 
	do m <- modname # getStBr
	   pfePut (toNodeInfo (Right (m,lbl)))

    followLink lbl def = rememberLbl lbl >> goto def

    changeHilite new =
      do old <- hilbls # getStBr
	 pfePut (toSource (hilite (old\\new) (new\\old)))
	 updStBr $ \st->st{hilbls=new}

    getIdInfo lbl@(Lbl token) =
      do refs <- mrefs # getStBr
	 infixes <- getModuleInfixes
	 path <- fst . modnode # getStBr
	 let p = (path,lblPos lbl)
	     (occurences,optdef,refinfo) = idInfo refs infixes token
	 return ((occurences,optdef,concatMap msglines refinfo),p)

    fromSource (Just (Button 1),lbl@(Lbl ((ModuleName,(_,mn)),_))) =
	newModule (PlainModule mn) -- !!!
    fromSource (Just button,lbl@(Lbl token)) =
	case button of
	  Button 1 -> case isCertTokenRef token of
			Just cert -> changeHilite [lbl] >> updCertInfo cert
			_ -> do info@((_,optdef,_),_) <- getIdInfo lbl
				case optdef of
				  Nothing -> done
				  Just def ->
				    if isDefLbl lbl
				    then showInfo' lbl info
				    else followLink lbl def
	  Button 2 -> showInfo lbl
	  Button 3 -> do ((occurences,_,refinfo),_) <- getIdInfo lbl
			 let cnt=length occurences
			     msg=if cnt>0
				 then ["Highlighted all "++show cnt++
					" occurences in this module"]
				 else []
			 changeHilite (map posLabel occurences)
			 pfePut (toRefs (linesD (map g (refinfo++msg))))
	  _ -> done
    fromSource (Nothing,lbl) =
	ifM (isLink lbl)
	    (pfePut (toSource setlinkcursor))
	    (pfePut (toSource setnormalcursor))
      where
	isLink (Lbl ((ModuleName,(_,mn)),_)) = return True
	isLink lbl = 
	  if isDefLbl lbl
	  then return False
	  else do info@((_,optdef,_),_) <- getIdInfo lbl
		  return (isJust optdef)

    updCertInfo cert = showCertInfo cert >> updCertIcons cert

    updCertIcons cert = whenM (statusChange cert) reloadModule
       -- TODO: efficient icon updates in the source display and evidence window

    showInfo lbl = showInfo' lbl =<< getIdInfo lbl

    showInfo' lbl ((_,def,refinfo),p) =
	do --optGetTypes
	   tinfo <- maybeD (optGetType p) def
	   ainfo <- maybeD getAssertionInfo def
	   pfePut (toRefs (linesD (map g refinfo++ainfo++tinfo)))
	   changeHilite (if isJust def then [lbl] else [])
      where
	maybeD = maybe (return [])

	optGetType p o = maybe (return []) (getType p o) . types =<< getStBr

	getType p (qn,k) types =
	  do --print (k,qn)
	     m <- modname # getStBr
	     let env = modtypes m types
	     o <- ppFlags
	     --print (let xs:>:_ = unzipTyped mt in xs)
	     return [typeInfo o env k p qn]

	typeInfo ppopts (mt,env) k p qn =
	    if isClassOrType k
	    then kinfo qn (fst env)
	    else tinfo (snd (no_use env)) mt p qn
	 where
	    kinfo qn = optpp . lookup qn . convTEnv (ppi.fst)

	    optpp = maybe (Fud.g "No type/kind info available") (ppo ppopts)

	    tinfo env mt (path,lexpos) qn =
		optpp (find' mt `mplus` lookup qn env')
	      where env' = convTEnv (ppi.fst) (env++mt)
		    qn' = getHSName qn
		    find' = fmap pp_use . find (pos.name)
		    name (i:>:_) = getHSName i
		    pos (PNT pn _ (N (Just (SrcLoc f _ lin col)))) =
		      pn==qn' && f==path && col==column lexpos && lin==line lexpos
		    pos i = False
		    pp_use (_:>:(gen,opti)) =
		      case opti of
			Just inst -> "Generally:"<+>gen<>","$$"Here:"<+>inst
			_ -> ppi gen

		    pntpos (PNT _ _ (N p)) = p

	convTEnv f env = [(bn i,f info)|i:>:info<-env]
	  where
	    bn = fmap orig -- . getHSName
	    orig (PNT n _ _) = n

	modtypes m pfe4info = (snd (envFrom tm),(concat kenvs,concat tenvs))
	  where
	    Just (_,((_,tm):_,_)) = lookup m (pfe4info::TInfo)
	    (kenvs,tenvs) = unzip [env|(_,(_,(_,(_,env))))<-pfe4info]

    optGetTypes =
      do st <- getStBr
	 when (viewMode st==Typed &&
               not (isNoModule (modnode st) || haveTypes st))
	      (retypeCheck (modname st))
      where
        retypeCheck m =
	     withWaitMsg (g "Type checking...") $
	     do setStatus (Typing,InProgress)
                opttypes <- exTypeCheck (Just [m])
		case opttypes of
		  Left err -> typeErrorHandler err
		  Right types ->
		    do mIface <- moduleInterface m -- calls typeCheck again ==> slow!!
		       setStatus (Typing,Good)
		       o <- ppFlags
		       putInfoWindow (Interface,ppo o (ppIface mIface))
		       updStBr $ \st->st{types=Just types}

    clearRefs = pfePut (toRefs (blankD 10))

    popupMsg = pfePut . toMessagePopup . msglines

    withWaitMsg msg cmd =
      do pfePut (toRefs msg)
	 tryThen (withWaitCursor cmd) $ clearRefs

setInProgress cmds =
    do updStBr $ \ st -> st{certInProgress=cmds}
       o <- ppFlags
       putInfoWindow (PendingCmds,ppo o (vcat cmds))

ppMsgGfx o = msgGfx . ppu o
msgGfx = linesD . map g . msglines
--msgGfx = vboxlD' 0 . map (atomicD . expandTabs 8)

ppo ppopts = ppo' ppopts
ppo' (_,ppopts) = fontD ppfont . drawDoc . withPPEnv ppopts . ppi

msglines = map (expandTabs 8) . lines

clickToActivate = 
--  "(To activate type checker: click with the middle mouse button on an identifier)"
  "(To activate type checker: select Type Info from the View menu)"

---
{-
instance CatchIO e m => CatchIO e (WithState s m) where
  stm `catch` h =  do s <- getSt
		      r <- lift $ try (withStS s stm)
		      case r of
			Left err -> h err
			Right (ans,s') -> setSt_ s' >> return ans
  ioError = lift . ioError
-}

--
ppfont = argKey "ppfont" refFont
