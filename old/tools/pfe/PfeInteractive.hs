module PfeInteractive(pfeiCmd,pfeiAllCmds,runSIO) where
import Prelude hiding (getContents,print,catch,putStrLn,writeFile)
import AbstractIO
import PfeParse
import PFE0(projectStatus,checkProject,setBatchMode,withProjectDir',newProjectHelp)
import Pfe0Cmds(addHelpCmd)
import PfeSocket(listenOnPFE,acceptPFE,removePFE,serverOps,sResult,errorString)

import qualified IO
import SIO

pfeiAllCmds pfeCmds prg = addHelpCmd prg (pfeCmds++pfeiCmd pfeCmds prg)

pfeiCmd pfeCmds prg =
    [("interactive",(noArgs pfeI,"read pfe commands from stdin")),
     ("server",     (noArgs pfeS,"start a PFE server"))]
  where
    pfeI =
      do setBatchMode False
         putStrLn "--- pfe interactive starts ---"
         mapM_ (doPfeCmd . words) . lines =<< getContents
	 putStrLn "--- pfe interactive ends ---"

    doPfeICmd cmd =
      do doPfeCmd cmd `catch` printError
         putStrLn "--- pfe interactive ---"

    doPfeCmd cmd = doCmd (pfeCmds',projectStatus) prg cmd

    pfeCmds' = addHelpCmd prg pfeCmds

    pfeS =
      do --s <- inBase $ listenOn (PortNumber 9999)
	 --withServerFile (flip writeFile "9999")
	 s <- withProjectDir'' (inBase . listenOnPFE)
	 setBatchMode False
	 tryThen (loop $ server s) (withProjectDir'' (inBase . removePFE))

    server s =
      do (h,host,port) <- inBase $ acceptPFE s
	 --print (host,port)
	 r <- try $ withStdio (serverOps h) (serve h)
	 inBase $ sResult h r
	 --putStrLn "done"
	 inBase $ IO.hClose h
      where
        serve h = doPfeCmd . words =<< inBase (IO.hGetLine h)


withProjectDir'' m = withProjectDir' newProjectHelp m

loop m = l where l = m >> l

printError e = ePutStrLn (errorString e)
