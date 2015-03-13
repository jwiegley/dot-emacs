module PfeAlfaCmds(pfeAlfaCmds) where
import Prelude hiding (putStrLn,writeFile,catch)
import Monad(filterM)
import Maybe(mapMaybe)
import List(intersect)

import HsModule

import RemovePatBinds(remPats)
import RemoveListCompProp(rmAllListComp)
import SimpFunBind(simpAllFunBind)
import SimpPatMatch(simpAllPatMatch,getSimpPatIds,prelError)
--import SimpFieldLabels(simpFieldLabels)
import DefinedNames(addName)
import PFE4(rewriteAndTypeCheck)
import PFE_Rewrites(Rewrite(..),compRw,pmRewrite,pbRewrite,lcRewrite)
import PFE0(moduleList,subGraph,newerThan,getSortedSubGraph)
import PfeParse(moduleArgs',kwOption,just)
import TI((+++))
import TiModule(joinModules,representative)

import Prop2Alfa(transModule,modPath)
import BaseStruct2Alfa(packageSynonym,joinModuleNames)
--import FileConv(printModule)
import qualified UAbstract as U

import AbstractIO
import DirUtils(getModificationTimeMaybe)
import MUtils
import EnvM(withEnv)

pfeAlfaCmds =
  [--("alfa",(moduleArgs prop2alfa1,"translate modules to Alfa")),
   ("alfa",(moduleArgs' opt prop2alfa,"translate modules to Alfa"))]
  where
    opt = kwOption "-simplepats"

prop2alfa simplepats = if simplepats then prop2alfa2 else prop2alfa1

prop2alfa1 = prop2alfa' rewrite1
prop2alfa2 = prop2alfa' rewrite2

rewrite1 = pmRewrite `compRw` rewrite2
rewrite2 = pbRewrite `compRw` lcRewrite `compRw` addNameRw
addNameRw = Rewrite "an" (return addName)

prop2alfa' rewrite@(Rewrite rwname _) ms =
    do dir <- getEnv "APFE_DIR" `catch` const (return "alfa")
       changedsccs <- changedSccs dir =<< getSortedSubGraph (just ms)
       let ms = concat changedsccs
       if null ms then done
         else do tms <- rewriteAndTypeCheck rewrite  (Just ms)
                 mapM_ (transSCC dir tms) changedsccs
  where
    transSCC dir alltms ms = mapM (writeModule dir . trans1) ms
      where
        joinedmn = joinModuleNames ms
	rm = representative ms
	tms = [(m,tm)|(m,(_,(tms,_)))<-alltms,m `elem` ms,(rwn,tm)<-tms,rwn==rwname++"fl"]
	joinedtm = joinModules (map snd tms)

        trans1 m = (m,U.Module transm)
          where
            transm = if m==rm
	             then transds ++ syn
	             else imp:syn

            U.Module transds = withEnv (ms,env) (transModule joinedtm)
            syn = if m==joinedmn then [] else packageSynonym m joinedmn
	    imp = U.ImportDecl (U.Import (modPath rm))

        env = foldr ((+++).snd.snd.snd.snd) ([],[]) alltms

{-
prop2alfa1 =
    mapM_ writeModule.transModules @@ rewriteAndTypeCheck rewrite.Just
  where
    transModules ms = mapMaybe transModule' ms
      where
        transModule' (n,(_,(optm,_))) =
	    do m <- optm
	       return (n,withEnv ([n],env) (transModule m))
        env = foldr ((+++).snd.snd.snd.snd) ([],[]) ms
-}

writeModule dir (n,U.Module decls) =
    do let path=dir++"/"++modPath n
       ePutStrLn ("Updating: "++path)
       writeFile path ({-printModule-}show m)
  where
    m = U.Module (prefix++decls)
    prefix =
      [ U.Comment magic,
	U.ImportDecl (U.Import "Haskell.alfa"),
        U.Comment "{-# Alfa hidetypeannots on #-}"]

    magic = "-- Automatically converted from Haskell by hs2alfa..."

changedSccs dir g =
    -- A quick hack to avoid retranslating unchanged modules...
    do changed <- map (fst.snd) # filterM moduleChanged (concat g)
       let allsccs = [[m|(f,(m,is))<-scc]|scc<-g]
	   sccs= [scc|scc<-allsccs,
		      not.null $
		      moduleList (subGraph g scc) `intersect` changed]
       return sccs
  where
    moduleChanged (path,(m,_)) =
      newerThan  # getModificationTime path
                <# getModificationTimeMaybe (dir++"/"++modPath m)

