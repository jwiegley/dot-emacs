module PFE_HTML where
import Prelude hiding(putStrLn,writeFile)
--import Maybe(fromJust)
import Control.Monad(when,unless)

--import HsName(ModuleName(Module))
--import ScopeModule(scopeModule)

import ConvRefsTypes(simplifyRefsTypes')
import HLex2html(hlex2html')
import HsLexerPass1(line,column) -- hmm

import PFE0(findFile,newerThan,getCurrentModuleGraph,allModules,checkProject,moduleInfoPath)
import PFE2(getModuleTime)
import PFE3(parseSourceFile'')

import PathUtils(normf)
import DirUtils(getModificationTimeMaybe,optCreateDirectory)
--import FileUtils(updateFile)
import AbstractIO
--import MUtils
import PrettyPrint(pp)

toHtmlFiles outDir srcURL modHTML optms =
    do ms <- maybe allModules return optms
       dir <- checkProject
       unless (null ms) $ optCreateDirectory (outDir dir)
       mapM_ (module2html dir) ms
  where
    module2html dir m =
      do let out_path = outDir dir++htmlFile m
	 t_mod <- getModuleTime m
	 t_html <- getModificationTimeMaybe out_path
	 when (t_mod `newerThan` t_html) $ -- hmm!!
	      do putStrLn $ "Updating: "++out_path
                 writeFile out_path =<< file2html srcURL m

    file2html srcURL m =
      do path <- findFile m
	 g <- getCurrentModuleGraph
	 (ts,(_,rs0)) <- parseSourceFile'' path
	 let rs = simplifyRefsTypes' rs0
	     ffm = (path,[(normf f,m)|(f,(m,_))<-g])
	 return (modHTML m (hlex2html' srcURL ffm (rs,ts)))

--------------------------------------------------------------------------------

htmlFile m = moduleInfoPath m++".html"

htmlDir dir = dir++"html/"
--htmlPath m dir = htmldir dir++htmlFile m

wwwDir  dir = dir++"www/"
--wwwPath m dir = wwwdir dir++htmlFile m

--------------------------------------------------------------------------------
