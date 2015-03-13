{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}


import GHC.Generics

import Bag
import Bag(Bag,bagToList)
-- import Data.Generics
import FastString(FastString)
import GHC.Paths ( libdir )
import GHC.SYB.Utils
import RdrName
import OccName
import qualified OccName(occNameString)


-----------------

import qualified Data.Generics.Schemes as SYB
import qualified Data.Generics.Aliases as SYB
import qualified GHC.SYB.Utils         as SYB

import Var
import qualified CoreFVs               as GHC
import qualified CoreSyn               as GHC
import qualified DynFlags              as GHC
import qualified ErrUtils              as GHC
import qualified Exception             as GHC
import qualified FastString            as GHC
import qualified GHC                   as GHC
import qualified HscTypes              as GHC
import qualified Lexer                 as GHC
import qualified MonadUtils            as GHC
import qualified Outputable            as GHC
import qualified SrcLoc                as GHC
import qualified StringBuffer          as GHC

import GHC.Paths ( libdir )

-----------------

import Language.Haskell.Refact.Utils
import Language.Haskell.Refact.Utils.GhcUtils
import Language.Haskell.Refact.Utils.LocUtils
import Language.Haskell.Refact.Utils.Monad
import Language.Haskell.Refact.Utils.TokenUtils
import Language.Haskell.Refact.Utils.TypeUtils
import qualified Language.Haskell.Refact.Case as GhcRefacCase
import qualified Language.Haskell.Refact.SwapArgs as GhcSwapArgs

import Control.Monad.State

import Control.Applicative
import Data.Data
import Data.IORef
import System.Directory
import System.FilePath
import qualified Data.Map as Map

-- import Language.Haskell.Refact.Utils.GhcUtils


-- targetFile = "./refactorer/" ++ targetMod ++ ".hs"

-- targetFile = "./test/testdata/" ++ targetMod ++ ".hs"
-- targetMod = "FreeAndDeclared/Declare"

--targetFile = "../test/testdata/" ++ targetMod ++ ".hs"

-- ++AZ++ targetFile = "./test/testdata/TypeUtils/" ++ targetMod ++ ".hs"
--targetFile = "./" ++ targetMod ++ ".hs"
-- targetMod = "SwapArgs/B"
-- targetMod = "Ole"
-- ++AZ++ targetMod = "Empty"

targetFile = "./test/testdata/" ++ targetMod ++ ".hs" -- ++AZ++
-- targetMod = "Demote/WhereIn6"                                       -- ++AZ++
-- targetMod = "MoveDef/Md1"                                       -- ++AZ++
-- targetMod = "Demote/WhereIn2"                                       -- ++AZ++
-- targetMod = "Demote/PatBindIn1"                                       -- ++AZ++
targetMod = "BCpp"                                       -- ++AZ++

main = putStrLn "main"

p1 =
  do
    toks <- lexStringToRichTokens (GHC.mkRealSrcLoc (GHC.mkFastString "foo") 0 0) "if (1) then x else y"
    putStrLn $ showToks toks


-- data HsExpr id
--   ...
--   HsIf (Maybe (SyntaxExpr id)) (LHsExpr id) (LHsExpr id) (LHsExpr id)
--                                  ^1            ^2           ^3
--   ...
--  HsCase (LHsExpr id) (MatchGroup id)
--            ^1

-- data MatchGroup id
--   MatchGroup [LMatch id] PostTcType
-- type LMatch id = Located (Match id)
-- data Match id
--   Match [LPat id] (Maybe (LHsType id)) (GRHSs id)

getStuff =
#if __GLASGOW_HASKELL__ > 704
    GHC.defaultErrorHandler GHC.defaultFatalMessager GHC.defaultFlushOut $ do
#else
    GHC.defaultErrorHandler GHC.defaultLogAction $ do
#endif
      GHC.runGhc (Just libdir) $ do
        dflags <- GHC.getSessionDynFlags
        let dflags' = foldl GHC.xopt_set dflags
                           [GHC.Opt_Cpp, GHC.Opt_ImplicitPrelude, GHC.Opt_MagicHash]

            dflags'' = dflags' { GHC.importPaths = ["./test/testdata/","../test/testdata/"] }

            dflags''' = dflags'' { GHC.hscTarget = GHC.HscInterpreted,
                                   GHC.ghcLink =  GHC.LinkInMemory }

        GHC.setSessionDynFlags dflags'''
        GHC.liftIO $ putStrLn $ "dflags set"

        target <- GHC.guessTarget targetFile Nothing
        GHC.setTargets [target]
        GHC.liftIO $ putStrLn $ "targets set"
        GHC.load GHC.LoadAllTargets -- Loads and compiles, much as calling make
        GHC.liftIO $ putStrLn $ "targets loaded"
        -- modSum <- GHC.getModSummary $ GHC.mkModuleName "B"
        -- modSum <- GHC.getModSummary $ GHC.mkModuleName "FreeAndDeclared.Declare"
        -- modSum <- GHC.getModSummary $ GHC.mkModuleName "SwapArgs.B"
        -- modSum <- GHC.getModSummary $ GHC.mkModuleName "Ole"
        -- ++AZ++ modSum <- GHC.getModSummary $ GHC.mkModuleName targetMod 
        -- modSum <- GHC.getModSummary $ GHC.mkModuleName "Demote.WhereIn6"
        -- modSum <- GHC.getModSummary $ GHC.mkModuleName "MoveDef.Md1"
        -- modSum <- GHC.getModSummary $ GHC.mkModuleName "Demote.WhereIn2"
        -- modSum <- GHC.getModSummary $ GHC.mkModuleName "Demote.PatBindIn1"
        modSum <- GHC.getModSummary $ GHC.mkModuleName "BCpp"
        GHC.liftIO $ putStrLn $ "got modsummary"
        p <- GHC.parseModule modSum
        GHC.liftIO $ putStrLn $ "parsed"

        t <- GHC.typecheckModule p
        GHC.liftIO $ putStrLn $ "type checked"
        d <- GHC.desugarModule t
        l <- GHC.loadModule d
        n <- GHC.getNamesInScope
        -- c <- return $ GHC.coreModule d
        c <- return $ GHC.coreModule d

#if __GLASGOW_HASKELL__ > 704
        GHC.setContext [GHC.IIModule (GHC.moduleName $ GHC.ms_mod modSum)]
#else
        GHC.setContext [GHC.IIModule (                 GHC.ms_mod modSum)]
#endif

        -- GHC.setContext [GHC.IIModule (GHC.ms_mod modSum)]
        inscopes <- GHC.getNamesInScope
        GHC.liftIO $ putStrLn $ "got inscopes"


        g <- GHC.getModuleGraph
        gs <- mapM GHC.showModule g
        GHC.liftIO (putStrLn $ "modulegraph=" ++ (show gs))
        -- return $ (parsedSource d,"/n-----/n",  typecheckedSource d, "/n-=-=-=-=-=-=-/n", modInfoTyThings $ moduleInfo t)
        -- return $ (parsedSource d,"/n-----/n",  typecheckedSource d, "/n-=-=-=-=-=-=-/n")
        -- return $ (typecheckedSource d)

        -- res <- getRichTokenStream (ms_mod modSum)
        -- return $ showRichTokenStream res

        {-
        let ps = convertSource $ pm_parsed_source p
        let res = showData Parser 4 ps
        -- let res = showPpr ps
        return res
        -}
        -- let p' = processParsedMod ifToCase t
        -- GHC.liftIO (putStrLn . showParsedModule $ t)
        -- GHC.liftIO (putStrLn . showParsedModule $ p')
        -- GHC.liftIO (putStrLn $ showGhc $ GHC.tm_typechecked_source p')

        let ps  = GHC.pm_parsed_source p
        GHC.liftIO $ putStrLn $ "got parsed source"
        -- GHC.liftIO (putStrLn $ SYB.showData SYB.Parser 0 ps)
        -- GHC.liftIO (putStrLn $ show (modIsExported ps))
        -- _ <- processVarUniques t



        -- Tokens ------------------------------------------------------
        ts <- GHC.getTokenStream (GHC.ms_mod modSum)
        GHC.liftIO $ putStrLn $ "got ts"
        rts <- GHC.getRichTokenStream (GHC.ms_mod modSum)
        GHC.liftIO $ putStrLn $ "got rts"
        -- GHC.liftIO (putStrLn $ "tokens=" ++ (showRichTokenStream rts))
        -- GHC.liftIO (putStrLn $ "tokens=" ++ (show $ tokenLocs rts))
        -- GHC.liftIO (putStrLn $ "tokens=" ++ (show $ map (\(GHC.L _ tok,s) -> (tok,s)) rts)) 
        -- GHC.liftIO (putStrLn $ "tokens=" ++ (showToks rts))

        -- addSourceToTokens :: RealSrcLoc -> StringBuffer -> [Located Token] -> [(Located Token, String)]
        -- let tt = GHC.addSourceToTokens (GHC.mkRealSrcLoc (GHC.mkFastString "f") 1 1) (GHC.stringToStringBuffer "hiding (a,b)") []
        -- GHC.liftIO (putStrLn $ "new tokens=" ++ (showToks tt))


        -- GHC.liftIO (putStrLn $ "ghcSrcLocs=" ++ (show $ ghcSrcLocs ps))
        -- GHC.liftIO (putStrLn $ "srcLocs=" ++ (show $ srcLocs ps))

        -- GHC.liftIO (putStrLn $ "locToExp=" ++ (showPpr $ locToExp (4,12) (4,16) rts ps))
        -- GHC.liftIO (putStrLn $ "locToExp=" ++ (SYB.showData SYB.Parser 0 $ locToExp (4,12) (4,16) rts ps))
        -- GHC.liftIO (putStrLn $ "locToExp1=" ++ (SYB.showData SYB.Parser 0 $ locToExp (4,8) (4,43) rts ps))
        -- GHC.liftIO (putStrLn $ "locToExp2=" ++ (SYB.showData SYB.Parser 0 $ locToExp (4,8) (4,40) rts ps))


        -- Inscopes ----------------------------------------------------
        -- GHC.liftIO (putStrLn $ "\ninscopes(showData)=" ++ (SYB.showData SYB.Parser 0 $ inscopes))
        -- names <- GHC.parseName "G.mkT"
        -- GHC.liftIO (putStrLn $ "\nparseName=" ++ (showGhc $ names))


        -- ParsedSource -----------------------------------------------
        -- GHC.liftIO (putStrLn $ "parsedSource(Ppr)=" ++ (showGhc $ GHC.pm_parsed_source p))
        -- GHC.liftIO (putStrLn $ "\nparsedSource(showData)=" ++ (SYB.showData SYB.Parser 0 $ GHC.pm_parsed_source p))

        -- RenamedSource -----------------------------------------------
        GHC.liftIO $ putStrLn $ "about to show renamedSource"

        GHC.liftIO (putStrLn $ "renamedSource(Ppr)=" ++ (showGhc $ GHC.tm_renamed_source t))
        GHC.liftIO (putStrLn $ "\nrenamedSource(showData)=" ++ (SYB.showData SYB.Renamer 0 $ GHC.tm_renamed_source t))

        -- GHC.liftIO (putStrLn $ "typeCheckedSource=" ++ (showGhc $ GHC.tm_typechecked_source t))
        -- GHC.liftIO (putStrLn $ "typeCheckedSource=" ++ (SYB.showData SYB.TypeChecker 0 $ GHC.tm_typechecked_source t))

        -- ModuleInfo ----------------------------------------------------------------
        -- GHC.liftIO (putStrLn $ "moduleInfo.TyThings=" ++ (SYB.showData SYB.Parser 0 $ GHC.modInfoTyThings $ GHC.tm_checked_module_info t))
        -- GHC.liftIO (putStrLn $ "moduleInfo.TyThings=" ++ (showGhc $ GHC.modInfoTyThings $ GHC.tm_checked_module_info t))
        -- GHC.liftIO (putStrLn $ "moduleInfo.TopLevelScope=" ++ (showGhc $ GHC.modInfoTopLevelScope $ GHC.tm_checked_module_info t))


        -- Investigating TypeCheckedModule, in t
        --GHC.liftIO (putStrLn $ "TypecheckedModule : tm_renamed_source(Ppr)=" ++ (showGhc $ GHC.tm_renamed_source t))
        --GHC.liftIO (putStrLn $ "TypecheckedModule : tm_renamed_source(showData)=" ++ (SYB.showData SYB.Parser 0 $ GHC.tm_renamed_source t))

        -- GHC.liftIO (putStrLn $ "TypecheckedModule : tm_typechecked_source(Ppr)=" ++ (showGhc $ GHC.tm_typechecked_source t))
        -- GHC.liftIO (putStrLn $ "TypecheckedModule : tm_typechecked_source(showData)=" ++ (SYB.showData SYB.Parser 0 $ GHC.tm_typechecked_source t))


        -- Core module -------------------------------------------------
        -- GHC.liftIO (putStrLn $ "TypecheckedModuleCoreModule : cm_binds(showData)=" ++ (SYB.showData SYB.TypeChecker 0 $ GHC.mg_binds c))

        -- GHC.liftIO (putStrLn $ "TypecheckedModuleCoreModule : cm_binds(showData)=" ++ (SYB.showData SYB.TypeChecker 0 $ GHC.exprsFreeVars $ getBinds $ GHC.mg_binds c))
        -- GHC.liftIO (putStrLn $ "TypecheckedModuleCoreModule : exprFreeVars cm_binds(showData)=" ++ (showGhc $ GHC.exprsFreeVars $ getBinds $ GHC.mg_binds c))
        -- GHC.liftIO (putStrLn $ "TypecheckedModuleCoreModule : exprFreeIds cm_binds(showPpr)=" ++ (showGhc $ map GHC.exprFreeIds $ getBinds $ GHC.mg_binds c))

        -- GHC.liftIO (putStrLn $ "TypecheckedModuleCoreModule : bindFreeVars cm_binds(showPpr)=" ++ (showGhc $ map GHC.bindFreeVars $ GHC.mg_binds c))


        return ()


-- |Show a GHC API structure
showGhc :: (GHC.Outputable a) => a -> String
#if __GLASGOW_HASKELL__ > 704
showGhc x = GHC.showSDoc GHC.tracingDynFlags $ GHC.ppr x
#else
showGhc x = GHC.showSDoc                     $ GHC.ppr x
#endif

-- ---------------------------------------------------------------------


deriving instance Generic (GHC.HsExpr a)





