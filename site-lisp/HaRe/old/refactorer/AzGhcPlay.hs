-- Sample refactoring based on ifToCase


import Bag
import Bag(Bag,bagToList)
import Data.Generics
-- import DynFlags
import FastString(FastString)
-- import GHC
import GHC.Paths ( libdir )
import GHC.SYB.Utils
import Name
import NameSet(NameSet,nameSetToList)
import Outputable
import PprTyThing
import SrcLoc
import Var(Var)
import RdrName
import OccName
import qualified OccName(occNameString)


-----------------
import qualified Data.Generics.Schemes as SYB
import qualified Data.Generics.Aliases as SYB
import qualified GHC.SYB.Utils         as SYB

import qualified GHC
import qualified DynFlags              as GHC
import qualified Outputable            as GHC
import qualified MonadUtils            as GHC
import qualified FastString            as GHC
import qualified SrcLoc                as GHC

import GHC.Paths ( libdir )
 
-----------------

import GhcRefacLocUtils
import GhcRefacUtils
import qualified GhcRefacCase as GhcRefacCase
-- import qualified GhcRefacRename as GhcRefacRename
import GhcUtils

-- targetFile = "./refactorer/" ++ targetMod ++ ".hs"
targetFile = "./" ++ targetMod ++ ".hs"
-- targetFile = "B.hs"
targetMod = "B"


t1 = GhcRefacCase.ifToCase ["./refactorer/B.hs","4","7","4","43"]
t2 = GhcRefacCase.ifToCase ["./B.hs","4","7","4","43"]


-- added by Chris for renaming
-- r1 = GhcRefacRename.rename ["./C.hs", "NewBlah", "4", "1"]



p1 = 
  do
    toks <- lexStringToRichTokens (GHC.mkRealSrcLoc (GHC.mkFastString "foo") 0 0) "if (1) then x else y"
    putStrLn $ showToks toks



-- import RefacUtils 
{-
ifToCase args  
  = do let fileName = args!!0              
           beginPos = (read (args!!1), read (args!!2))::(Int,Int)
           endPos   = (read (args!!3), read (args!!4))::(Int,Int)
       modInfo@(_, _, mod, toks) <- parseSourceFile fileName 
       let exp = locToExp beginPos endPos toks mod
       case exp of 
           (Exp (HsIf _ _ _))   
                -> do refactoredMod <- applyRefac (ifToCase exp) (Just modInfo) fileName          
                      writeRefactoredFiles False [refactoredMod]
           _   -> error "You haven't selected an if-then-else  expression!"
    where 

     ifToCase exp (_, _, mod)= applyTP (once_buTP (failTP `adhocTP` inExp)) mod
       where 
         inExp exp1@((Exp (HsIf  e e1 e2))::HsExpP)
           | sameOccurrence exp exp1       
           = let newExp =Exp (HsCase e [HsAlt loc0 (nameToPat "True") (HsBody e1) [],
                                        HsAlt loc0 (nameToPat "False")(HsBody e2) []])
             in update exp1 newExp exp1
         inExp _ = mzero
-}

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
    GHC.defaultErrorHandler GHC.defaultLogAction $ do
      GHC.runGhc (Just libdir) $ do
        dflags <- GHC.getSessionDynFlags
        let dflags' = foldl GHC.xopt_set dflags
                            [GHC.Opt_Cpp, GHC.Opt_ImplicitPrelude, GHC.Opt_MagicHash]
        GHC.setSessionDynFlags dflags'
        target <- GHC.guessTarget targetFile Nothing
        GHC.setTargets [target]
        GHC.load GHC.LoadAllTargets -- Loads and compiles, much as calling make
        modSum <- GHC.getModSummary $ GHC.mkModuleName "B"
        p <- GHC.parseModule modSum
        
        t <- GHC.typecheckModule p
        d <- GHC.desugarModule t
        l <- GHC.loadModule d
        n <- GHC.getNamesInScope
        c <- return $ GHC.coreModule d

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
        let p' = processParsedMod ifToCase p
        -- GHC.liftIO (putStrLn . showParsedModule $ p)
        -- GHC.liftIO (putStrLn . showParsedModule $ p')
        GHC.liftIO (putStrLn $ showPpr $ GHC.pm_parsed_source p')

        let ps  = GHC.pm_parsed_source p

        rts <- GHC.getRichTokenStream (GHC.ms_mod modSum)
        -- GHC.liftIO (putStrLn $ "tokens=" ++ (showRichTokenStream rts))
        -- GHC.liftIO (putStrLn $ "tokens=" ++ (show $ tokenLocs rts))
        
        -- GHC.liftIO (putStrLn $ "ghcSrcLocs=" ++ (show $ ghcSrcLocs ps))
        -- GHC.liftIO (putStrLn $ "srcLocs=" ++ (show $ srcLocs ps))

        -- GHC.liftIO (putStrLn $ "locToExp=" ++ (showPpr $ locToExp (4,12) (4,16) rts ps))
        -- GHC.liftIO (putStrLn $ "locToExp=" ++ (SYB.showData SYB.Parser 0 $ locToExp (4,12) (4,16) rts ps))
        -- GHC.liftIO (putStrLn $ "locToExp1=" ++ (SYB.showData SYB.Parser 0 $ locToExp (4,8) (4,43) rts ps))
        -- GHC.liftIO (putStrLn $ "locToExp2=" ++ (SYB.showData SYB.Parser 0 $ locToExp (4,8) (4,40) rts ps))
        return ()

tokenLocs toks = map (\(L l _, s) -> (l,s)) toks

convertSource ps =1
  ps

ifToCase :: GHC.HsExpr GHC.RdrName -> GHC.HsExpr GHC.RdrName
--  HsIf (Maybe (SyntaxExpr id)) (LHsExpr id) (LHsExpr id) (LHsExpr id)
ifToCase (GHC.HsIf _se e1 e2 e3)
  = GHC.HsCase e1 (GHC.MatchGroup
                   [
                     (noLoc $ GHC.Match
                      [
                        noLoc $ GHC.ConPatIn (noLoc $ mkRdrUnqual $ mkVarOcc "True") (GHC.PrefixCon [])
                      ]
                      Nothing
                       ((GHC.GRHSs
                         [
                           noLoc $ GHC.GRHS [] e2
                         ] GHC.EmptyLocalBinds))
                      )
                   , (noLoc $ GHC.Match
                      [
                        noLoc $ GHC.ConPatIn (noLoc $ mkRdrUnqual $ mkVarOcc "False") (GHC.PrefixCon [])
                      ]
                      Nothing
                       ((GHC.GRHSs
                         [
                           noLoc $ GHC.GRHS [] e3
                         ] GHC.EmptyLocalBinds))
                      )
                   ] undefined)
ifToCase x                          = x

-- -----------------------------------------------------------------------------------------
-- From http://hpaste.org/65775
{-
   1. install first: ghc-paths, ghc-syb-utils
   2. make a file Test1.hs in this dir with what you want to parse/transform
   3 .run with: ghci -package ghc
-}

-- module Main where

 
main = example

example =
   GHC.runGhc (Just libdir) $ do
        dflags <- GHC.getSessionDynFlags
        let dflags' = foldl GHC.xopt_set dflags
                            [GHC.Opt_Cpp, GHC.Opt_ImplicitPrelude, GHC.Opt_MagicHash]
        GHC.setSessionDynFlags dflags'
        -- target <- GHC.guessTarget (targetMod ++ ".hs") Nothing
        target <- GHC.guessTarget targetFile Nothing
        GHC.setTargets [target]
        GHC.load GHC.LoadAllTargets
        modSum <- GHC.getModSummary $ GHC.mkModuleName targetMod
        p <- GHC.parseModule modSum
        let p' = processParsedMod shortenLists p
        -- GHC.liftIO (putStrLn . showParsedModule $ p)
        -- GHC.liftIO (putStrLn . showParsedModule $ p')
        GHC.liftIO (putStrLn $ showPpr $ GHC.pm_parsed_source p')

showParsedModule p = SYB.showData SYB.Parser 0 (GHC.pm_parsed_source p)

processParsedMod f pm = pm { GHC.pm_parsed_source = ps' }
  where
   ps  = GHC.pm_parsed_source pm
   -- ps' = SYB.everythingStaged SYB.Parser (SYB.mkT f) -- does not work yet
   -- everythingStaged :: Stage -> (r -> r -> r) -> r -> GenericQ r -> GenericQ r
   
   ps' :: GHC.ParsedSource
   ps' = SYB.everywhere (SYB.mkT f) ps -- exception
   -- ps' = everywhereStaged SYB.Parser (SYB.mkT f) ps 


shortenLists :: GHC.HsExpr GHC.RdrName -> GHC.HsExpr GHC.RdrName
shortenLists (GHC.ExplicitList t exprs) = GHC.ExplicitList t []
shortenLists x                          = x

-- ---------------------------------------------------------------------
{-
module B where
foo x = if (odd x) then \"Odd\" else \"Even\"
foo' x
  = case (odd x) of {
      True -> \"Odd\"
      False -> \"Even\" }
main = do { putStrLn $ show $ foo 5 }
mary = [1, 2, 3]"
*Main> :load "/home/alanz/mysrc/github/alanz/HaRe/refactorer/AzGhcPlay.hs"
[1 of 1] Compiling Main             ( /home/alanz/mysrc/github/alanz/HaRe/refactorer/AzGhcPlay.hs, interpreted )
Ok, modules loaded: Main.
*Main> 
*Main> 
*Main> 
*Main> getStuff
"
    (L {refactorer/B.hs:1:1} 
     (HsModule 
      (Just 
       (L {refactorer/B.hs:1:8} {ModuleName: B})) 
      (Nothing) 
      [] 
      [
       (L {refactorer/B.hs:4:1-41} 
        (ValD 
         (FunBind 
          (L {refactorer/B.hs:4:1-3} 
           (Unqual {OccName: foo})) 
          (False) 
          (MatchGroup 
           [
            (L {refactorer/B.hs:4:1-41} 
             (Match 
              [
               (L {refactorer/B.hs:4:5} 
                (VarPat 
                 (Unqual {OccName: x})))] 
              (Nothing) 
              (GRHSs 
               [
                (L {refactorer/B.hs:4:9-41} 
                 (GRHS 
                  [] 
                  (L {refactorer/B.hs:4:9-41} 
                   (HsIf 
                    (Just 
                     (HsLit 
                      (HsString {FastString: \"noSyntaxExpr\"}))) 
                    (L {refactorer/B.hs:4:12-18} 
                     (HsPar 
                      (L {refactorer/B.hs:4:13-17} 
                       (HsApp 
                        (L {refactorer/B.hs:4:13-15} 
                         (HsVar 
                          (Unqual {OccName: odd}))) 
                        (L {refactorer/B.hs:4:17} 
                         (HsVar 
                          (Unqual {OccName: x}))))))) 
                    (L {refactorer/B.hs:4:25-29} 
                     (HsLit 
                      (HsString {FastString: \"Odd\"}))) 
                    (L {refactorer/B.hs:4:36-41} 
                     (HsLit 
                      (HsString {FastString: \"Even\"})))))))] 
               (EmptyLocalBinds))))] {!type placeholder here?!}) 
          (WpHole) {!NameSet placeholder here!} 
          (Nothing)))),
       (L {refactorer/B.hs:(6,1)-(8,17)} 
        (ValD 
         (FunBind 
          (L {refactorer/B.hs:6:1-4} 
           (Unqual {OccName: foo'})) 
          (False) 
          (MatchGroup 
           [
            (L {refactorer/B.hs:(6,1)-(8,17)} 
             (Match 
              [
               (L {refactorer/B.hs:6:6} 
                (VarPat 
                 (Unqual {OccName: x})))] 
              (Nothing) 
              (GRHSs 
               [
                (L {refactorer/B.hs:(6,10)-(8,17)} 
                 (GRHS 
                  [] 
                  (L {refactorer/B.hs:(6,10)-(8,17)} 
                   (HsCase 
                    (L {refactorer/B.hs:6:15-21} 
                     (HsPar 
                      (L {refactorer/B.hs:6:16-20} 
                       (HsApp 
                        (L {refactorer/B.hs:6:16-18} 
                         (HsVar 
                          (Unqual {OccName: odd}))) 
                        (L {refactorer/B.hs:6:20} 
                         (HsVar 
                          (Unqual {OccName: x}))))))) 
                    (MatchGroup 
                     [
                      (L {refactorer/B.hs:7:3-15} 
                       (Match 
                        [
                         (L {refactorer/B.hs:7:3-6} 
                          (ConPatIn 
                           (L {refactorer/B.hs:7:3-6} 
                            (Unqual {OccName: True})) 
                           (PrefixCon 
                            [])))] 
                        (Nothing) 
                        (GRHSs 
                         [
                          (L {refactorer/B.hs:7:11-15} 
                           (GRHS 
                            [] 
                            (L {refactorer/B.hs:7:11-15} 
                             (HsLit 
                              (HsString {FastString: \"Odd\"})))))] 
                         (EmptyLocalBinds)))),
                      (L {refactorer/B.hs:8:3-17} 
                       (Match 
                        [
                         (L {refactorer/B.hs:8:3-7} 
                          (ConPatIn 
                           (L {refactorer/B.hs:8:3-7} 
                            (Unqual {OccName: False})) 
                           (PrefixCon 
                            [])))] 
                        (Nothing) 
                        (GRHSs 
                         [
                          (L {refactorer/B.hs:8:12-17} 
                           (GRHS 
                            [] 
                            (L {refactorer/B.hs:8:12-17} 
                             (HsLit 
                              (HsString {FastString: \"Even\"})))))] 
                         (EmptyLocalBinds))))] {!type placeholder here?!})))))] 
               (EmptyLocalBinds))))] {!type placeholder here?!}) 
          (WpHole) {!NameSet placeholder here!} 
          (Nothing)))),
       (L {refactorer/B.hs:(10,1)-(11,25)} 
        (ValD 
         (FunBind 
          (L {refactorer/B.hs:10:1-4} 
           (Unqual {OccName: main})) 
          (False) 
          (MatchGroup 
           [
            (L {refactorer/B.hs:(10,1)-(11,25)} 
             (Match 
              [] 
              (Nothing) 
              (GRHSs 
               [
                (L {refactorer/B.hs:(10,8)-(11,25)} 
                 (GRHS 
                  [] 
                  (L {refactorer/B.hs:(10,8)-(11,25)} 
                   (HsDo 
                    (DoExpr) 
                    [
                     (L {refactorer/B.hs:11:3-25} 
                      (ExprStmt 
                       (L {refactorer/B.hs:11:3-25} 
                        (OpApp 
                         (L {refactorer/B.hs:11:3-17} 
                          (OpApp 
                           (L {refactorer/B.hs:11:3-10} 
                            (HsVar 
                             (Unqual {OccName: putStrLn}))) 
                           (L {refactorer/B.hs:11:12} 
                            (HsVar 
                             (Unqual {OccName: $}))) {!fixity placeholder here?!} 
                           (L {refactorer/B.hs:11:14-17} 
                            (HsVar 
                             (Unqual {OccName: show}))))) 
                         (L {refactorer/B.hs:11:19} 
                          (HsVar 
                           (Unqual {OccName: $}))) {!fixity placeholder here?!} 
                         (L {refactorer/B.hs:11:21-25} 
                          (HsApp 
                           (L {refactorer/B.hs:11:21-23} 
                            (HsVar 
                             (Unqual {OccName: foo}))) 
                           (L {refactorer/B.hs:11:25} 
                            (HsOverLit 
                             (OverLit 
                              (HsIntegral 
                               (5)) 
                              (*** Exception: noRebindableInfo
   -}
