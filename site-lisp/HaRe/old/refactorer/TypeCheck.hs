module TypeCheck where

-- import System
import Unsafe.Coerce
import Control.Exception
import System.IO.Unsafe
import System.IO
import Data.List
--import PackageConfig    ( stringToPackageId )
import GHC hiding (SrcLoc)
-- import DynFlags (defaultDynFlags)
import DynFlags (defaultLogAction)
import HsSyn
import Outputable
import SrcLoc
--import AbstractIO
import Control.Monad
import Language.Haskell.Interpreter hiding (runGhc)
import Language.Haskell.Interpreter.Unsafe

-- import LocalSettings
import GHC.Paths ( libdir )
--GHC.Paths is available via cabal install ghc-paths

-- libdir = "/Library/Frameworks/GHC.framework/Versions/612/usr/lib/ghc-6.12.1"
targetFile = "/Users/chrisbrown/hare/tests/A1.hs"




ghcTypeCheck1 expr modName fileName =
  unsafePerformIO(
   do
      putStrLn "ghcTypeCheck1"
      putStrLn expr
      putStrLn modName
      putStrLn fileName
      
      -- Need to ignore warnings 
      -- r <- runInterpreter                   (testHint expr modName fileName)
      r <- unsafeRunInterpreterWithArgs ["-w"] (testHint expr modName fileName)
      
      case r of
         Left err -> do printInterpreterError err
                        return ""
         Right e -> return e
   )

-- observe that Interpreter () is an alias for InterpreterT IO ()
testHint :: String -> String -> String -> InterpreterT IO String
testHint expr modName fileName =
    do
      say $ "TypeCheck.testHint:(expr,modName,fileName)=" ++ (show (expr,modName,fileName)) -- ++AZ++
      -- say "Load SomeModule.hs"
      loadModules [fileName]
      --
      --say "Put the Prelude, Data.Map and *SomeModule in scope"
      --say "Data.Map is qualified as M!"
      setTopLevelModules [modName]
      setImportsQ [("Prelude", Nothing)]
      --
      say "Now we can query the type of an expression"
      let expr1 = modName ++ "." ++ expr
      say $ "e.g. typeOf " ++ expr1
      say =<< typeOf expr1
      return =<< typeOf expr1


say :: String -> Interpreter ()
say = liftIO . putStrLn

printInterpreterError :: InterpreterError -> IO ()
printInterpreterError e = error $ "Ups... " ++ (show e)

-- ++AZ++ these ghcXXX functions are new since 0.6.0.2
ghcInit args
 = unsafePerformIO (
    do
       return "GHC Initialised."
   )

ghcTypeCheck args modName =
 unsafePerformIO (
  do
   let newArgs = args ++ ".hs"
   -- ++AZ++ let packageConf = ghcPath
   -- ses     <- GHC.newSession {-JustTypecheck-} (Just (filter (/= '\n') packageConf))
   res <- doTypeCheck args modName
   return res)


doTypeCheck args modName = runGhc (Just libdir) $ do
   dflags0 <- GHC.getSessionDynFlags

   (dflags1,fileish_args,_) <- GHC.parseDynamicFlags dflags0 [noLoc "-fglasgow-exts"]
   GHC.setSessionDynFlags $ dflags1 {verbosity = 1, hscTarget=HscInterpreted , ghcLink=NoLink }
   target <- GHC.guessTarget args Nothing
   GHC.addTarget target
   f <- getSessionDynFlags
   res <- defaultCleanupHandler f (load LoadAllTargets)
   case res of
      Failed ->
        do
          error "Load Failed"
      Succeeded ->
        do
          -- putErrStrLn "Load succeded."
          m <- getModSummary (mkModuleName modName)
          checked <- (desugarModule =<< GHC.typecheckModule =<< GHC.parseModule m)   -- GHC.checkModule (mkModuleName modName) True
          let ts = typecheckedSource checked
          return ()

ghcTypeCheck3 expr modName =
   unsafePerformIO (
   do
      putStrLn "in ghcTypeCheck3"
      defaultErrorHandler defaultLogAction $ do
      -- ++AZ++ defaultErrorHandler defaultDynFlags $ do
      runGhc (Just libdir) $ do
        dflags <- getSessionDynFlags
        setSessionDynFlags dflags
        target <- guessTarget targetFile Nothing
        setTargets [target]
        load LoadAllTargets
        modSum <- getModSummary $ mkModuleName "A1"
        p <- parseModule modSum
        t <- typecheckModule p
        d <- desugarModule t
        l <- loadModule d
        n <- getNamesInScope
        c <- return $ coreModule d

        g <- getModuleGraph
        mapM showModule g
        return $ ("/n-----/n")


      {-defaultErrorHandler defaultDynFlags $ do
       runGhc (Just ghcPath) $ do

       dflags0 <- GHC.getSessionDynFlags
       (dflags1,fileish_args,_) <- GHC.parseDynamicFlags dflags0 [noLoc "-fglasgow-exts"]
       GHC.setSessionDynFlags $ dflags1 {verbosity = 1, hscTarget=HscInterpreted , ghcLink=NoLink }
       target <- GHC.guessTarget "/Users/chrisbrown/hare/test/A1.hs" Nothing
       GHC.addTarget target
       f <- getSessionDynFlags
       res <- defaultCleanupHandler f (load LoadAllTargets)
       m <- getModSummary (mkModuleName modName)
       checked <- (desugarModule =<< GHC.typecheckModule =<< GHC.parseModule m)   -- GHC.checkModule (mkModuleName modName) True
       let ts = typecheckedSource checked -}

        {-dflags <- getSessionDynFlags
        -- setSessionDynFlags dflags
        (dflags1,fileish_args,_) <- GHC.parseDynamicFlags dflags [noLoc "-fglasgow-exts"]
        GHC.setSessionDynFlags $ dflags1 {verbosity = 1, hscTarget=HscInterpreted , ghcLink=NoLink }

        target <- guessTarget "/home/chris/hare/HaRe_08072009/testing/addCon/A1.hs" Nothing
        setTargets [target]
        load LoadAllTargets
        modSum <- getModSummary $ (mkModuleName modName)
        checked <- (desugarModule =<< GHC.typecheckModule =<< GHC.parseModule modSum)   -- GHC.checkModule (mkModuleName modName) True
        l <- loadModule checked
        let ts = typecheckedSource checked -}
       --ty <- exprType  ("A1.over")
      {- ty <- getNamesInScope
       return "returned" -}
   )

ghcTypeCheckx ses2 expr modName =
  unsafePerformIO(
   do
       putStrLn ("in ghcTypeCheck1" ++ modName ++ expr)
       runGhc (Just libdir) $ do
       ty <- exprType  (modName ++ "." ++ expr)
       -- case res of
       --  Nothing -> error "GHC failed to load module."
       --  Just ty -> do
                      -- ty' <- cleanType ty
       return $ showSDoc $ ppr ty
  )
-- ++AZ++ end of these ghcXXX functions are new since 0.6.0.2

ghcTypeCheckPattern closure closure_name modName fileName =
  unsafePerformIO(
   do
      -- Need to ignore warnings
      -- r <- runInterpreter (testPattern closure closure_name modName fileName)
      r <- unsafeRunInterpreterWithArgs ["-w"] (testPattern closure closure_name modName fileName)
      case r of
         Left err -> do printInterpreterError err
                        return ""
         Right e -> return e
   )

testPattern :: String -> String -> String -> String -> InterpreterT IO String
testPattern closure closure_name modName fileName =
    do
      say fileName
      say modName
      -- say "Load SomeModule.hs"
      --
      --say "Put the Prelude, Data.Map and *SomeModule in scope"
      --say "Data.Map is qualified as M!"
      set [languageExtensions := [ImplicitPrelude,ExistentialQuantification, ScopedTypeVariables]]
      loadModules [fileName]
      setTopLevelModules [modName]
      setImportsQ [("Prelude", Nothing)]
      --
      say "Now we can query the type of an expression"
      let expr1 = closure
      say closure
      say closure_name
      say $ "e.g. typeOf " ++ expr1
      say =<< typeOf expr1
      -- say =<< typeOf closure_name
      return =<< typeOf expr1
{-
ghcTypeCheckPattern closure closure_name modName fileName =
  unsafePerformIO(
   do
       putStrLn "ghcTypeCheckPattern"
       runGhc (Just ghcPath) $ do
       usermod <- findModule  (mkModuleName modName) Nothing
       setContext [usermod] []
       r <- runStmt ("let " ++ closure) GHC.RunToCompletion
       ty <- exprType closure_name

       --case res of
       --  Nothing -> error "GHC failed to load module."
       --  Just ty -> do
                      -- ty' <- cleanType ty
       return $ showSDoc $ ppr ty
  ) -}

{- ghcEvalExpr args closure_call modName =
  unsafePerformIO(
   defaultErrorHandler defaultDynFlags $ do
   let newArgs = args ++ ".hs"
   let packageConf = ghcPath
   ses     <- GHC.newSession JustTypecheck (Just (filter (/= '\n') packageConf))
   dflags0 <- GHC.getSessionDynFlags ses

   (dflags1,fileish_args) <- GHC.parseDynamicFlags dflags0 ["-fglasgow-exts"]
   GHC.setSessionDynFlags $ dflags1 {verbosity = 1, hscTarget=HscInterpreted , ghcLink=NoLink }
   target <- GHC.guessTarget args Nothing
   GHC.addTarget target
   f <- getSessionDynFlags
   res <- defaultCleanupHandler f (load LoadAllTargets)
   case res of
      Failed ->
        do
          error "Load Failed"
      Succeeded ->
        do
          putErrStrLn "Load succeded."
          checked <- GHC.checkModule ses (mkModuleName modName) True
          case checked of
           Nothing   -> return "-1"
           Just cmod ->
             do
               usermod <- findModule ses (mkModuleName modName) Nothing
               putStrLn "d"
               setContext ses [usermod] []
               r <- runStmt ses (closure_call) GHC.RunToCompletion
               putStrLn "2"
               case r of
                GHC.RunOk names    -> do s <- nameToString ses (head names)
                                         case s of
                                          Nothing -> return "-1"
                                          Just x ->  return x
                GHC.RunFailed      -> error "* Failed"
                GHC.RunException e -> error $ "* Exception: " ++ show e
                GHC.RunBreak _ _ _ -> error "* Break."

               --  let ts = typecheckedSource cmod
               -- return ses


       putStrLn "first"
       -- f <- getSessionDynFlags ses2
       -- usermod <- defaultCleanupHandler f (findModule ses2 (mkModuleName modName) Nothing)
       dflags0 <- GHC.getSessionDynFlags ses2
       putStrLn "a"
       (dflags1,fileish_args) <- GHC.parseDynamicFlags dflags0 ["-fglasgow-exts"]
       putStrLn "b"
       GHC.setSessionDynFlags ses2 $ dflags1 {verbosity = 1, hscTarget=HscInterpreted , ghcLink=NoLink }
       putStrLn "c"
       usermod <- findModule ses2 (mkModuleName modName) Nothing
       putStrLn "d"
       setContext ses2 [usermod] []
       putStrLn "1"

    )

-- if -fglasgow-exts is on we show the foralls, otherwise we don't.
--  cleanType :: Type -> GHCi Type

ameToString :: GHC.Session -> Name -> IO (Maybe String)
nameToString cms name = do
        dflags  <- GHC.getSessionDynFlags cms
        -- let noop_log _ _ _ _ = return ()
        let expr = "show " ++ showSDoc (ppr name)
        -- GHC.setSessionDynFlags cms dflags{log_action=noop_log}
        mb_txt <- GHC.compileExpr cms expr
        case mb_txt of
            Just txt_ | txt <- unsafeCoerce txt_, not (null txt)
                      -> return $ Just txt
            _  -> return Nothing
-}


debugLog :: String -> b -> b
debugLog msg b =
  unsafePerformIO (
    do
      putErrStrLn msg
      return b
    )

logAndDump :: (Outputable a) => String -> a -> b -> b
logAndDump msg a b =
  unsafePerformIO (
    do
      putErrStrLn msg
      putErrStrLn $ showSDoc (ppr a)
      return b
    )

tidyFileName :: String -> String
tidyFileName ('.':'/':str) = str
tidyFileName str           = str

data Tag = Tag TagName TagFile TagLine TagDesc
  deriving (Eq)

instance Ord Tag where
  compare (Tag t1 _ _ _) (Tag t2 _ _ _) = compare t1 t2

instance Show Tag where
  show (Tag t f l d) = makeTagsLine t f l d

type TagName = String
type TagFile = String
type TagLine = Int
type TagDesc = String

makeTagsLine :: String -> String -> Int -> String -> String
makeTagsLine tag file line desc = tag `sep` file `sep` (show line) `sep` ";\t\"" ++ desc ++ "\""
  where a `sep` b = a ++ '\t':b


putErrStrLn = hPutStrLn stderr
putErrStr = hPutStr stderr
