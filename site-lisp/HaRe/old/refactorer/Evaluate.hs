-- module Evaluate where
module Main where

import System.Environment
import System.Exit
import Control.Exception
-- import System.IO.Unsafe
import System.IO
import Data.List
-- import Unsafe.Coerce
{-
-- Package GHC stuff
import GHC
import DynFlags
import ErrUtils
import PackageConfig
import HsSyn
import Outputable
import SrcLoc
import RdrName
import Name
-}
import Control.Monad
import Control.Monad.CatchIO
--import Language.Haskell.Interpreter hiding (runGhc)
import Language.Haskell.Interpreter
import Language.Haskell.Interpreter.Unsafe
-- import LocalSettings (evaluate_result)
import LocalSettings (evaluate,evaluate_result)
-- ---------------------------------------------------------------------
import qualified AbstractIO as AbstractIO
import System.IO.Unsafe
import System.Cmd
-- ---------------------------------------------------------------------

main
 = -- defaultErrorHandler defaultDynFlags $
   do
   ar <- getArgs
   putStrLn "here"
   let args = ar !! 0   -- ++AZ+++ This seems to be a filename
       -- newArgs = (ar !! 1) ++ "hs"
       closure_call = ar !! 1  -- ++AZ++ seems to be pretty print rendering of
       modName = ar !! 2
   -- error $ show (closure_call, modName, args)
   let newArgs =  args ++ ".hs"


   fc <- readFile args                              -- ++AZ++
   putStrLn ("File>>>>>\n" ++ fc ++ "\n<<<<<<<<\n") -- ++AZ++


   
   -- ++AZ++ let packageConf = ghcPath
   -- (eval_res, x) <- runEval args modName closure_call packageConf
   -- x <- runInterpreter (runEvalHint args modName closure_call)

   -- Need to ignore warnings 
   x <- unsafeRunInterpreterWithArgs ["-w"] (runEvalHint args modName closure_call)
                                     
   -- 
   case x of
     Left err -> do
                   printInterpreterError err
                   exitFailure -- Make exit code explicit
     Right x -> do putStrLn $ show (x)
                   writeFile evaluate_result x
                   exitSuccess -- Make exit code explicit


printInterpreterError :: InterpreterError -> IO ()
printInterpreterError e = error $ "Ups... " ++ (show e)


-- runInterpreter :: (MonadCatchIO m, Functor m) => InterpreterT m a -> m (Either InterpreterError a)
evalExpr
  :: (Functor m, MonadCatchIO m) =>
     String -> String -> ModuleName -> m (Either InterpreterError String)
evalExpr fileName closure_call modName = do
   -- x <- runInterpreter (runEvalHint fileName modName closure_call)
   -- return x
   fc <- liftIO $ readFile fileName
   return (Right $ fc)


runEvalHint
  :: MonadInterpreter m => String -> ModuleName -> String -> m String
runEvalHint fileName modName closure_call
 = do
      -- ++AZ++ : if this line is in, the loadmodules fails with missing Prelude 
      -- ++AZ++ set [languageExtensions := [OverlappingInstances]]

      loadModules [fileName]

      setTopLevelModules [modName]

      setImportsQ [("Prelude", Nothing)]
      let expr1 = (modName ++ "." ++ closure_call)

      -- eval :: MonadInterpreter m => String -> m StringSource
      -- eval expr will evaluate show expr. It will succeed only if expr has type t and there is a Show instance for t.

      a <- eval expr1 
      liftIO (putStrLn ("done evaluation: got...>" ++ (show a) ++ "<")) -- ++AZ++
      return a

-- NOTE ++AZ++ :this function not present in 0.6.0.2
{-
runEval args modName closure_call pac = runGhc (Just pac) $ do
   -- /usr/local/packages/ghc-6.6/lib/ghc-6.6
   --session     <- GHC.newSession {-JustTypecheck-} (Just (filter (/= '\n') packageConf))

   dflags0 <- getSessionDynFlags
   (f1,_,_) <- parseDynamicFlags dflags0 [noLoc "-fglasgow-exts", noLoc "-fno-monomorphism-restriction"]
   setSessionDynFlags f1{hscTarget = HscInterpreted,  ghcLink=NoLink}

   target <- GHC.guessTarget args Nothing

   -- (dflags1,fileish_args) <- GHC.parseDynamicFlags dflags0 []
   -- GHC.setSessionDynFlags session $ dflags1 {verbosity = 1, hscTarget=HscNothing}
   -- targets <- mapM (\a -> GHC.guessTarget a Nothing ) [args]
   GHC.addTarget {-session-} target

   GHC.load {-session-} GHC.LoadAllTargets

   -- findModule :: GhcMonad m => ModuleName -> Maybe FastString -> m Module
   usermod <- findModule (mkModuleName modName) Nothing
   -- setContext [usermod] []

   -- setContext :: GhcMonad m => [InteractiveImport] -> m ()
   setContext [IIModule usermod]

   r <- runStmt closure_call GHC.RunToCompletion

{-
RunOk [Name]	-- names bound by this evaluation
RunException SomeException	-- statement raised an exception
RunBreak ThreadId [Name] (Maybe BreakInfo)
-}

   case r of
       GHC.RunOk names    -> do s <- nameToString (head names)
                                case s of
                                          Nothing -> return (evaluate_result, "-1")  -- writeFile evaluate_result "-1"
                                          Just x ->  return (evaluate_result, x) -- writeFile evaluate_result x
       -- GHC.RunFailed      -> error "* Failed"
       GHC.RunException e -> error $ "* Exception: " ++ show e
       GHC.RunBreak _ _ _ -> error "* Break."


showNames :: [GHC.Name] -> String
showNames = Outputable.showSDoc . Outputable.ppr

nameToString :: Name -> Ghc (Maybe String)
nameToString name = do
        dflags  <- GHC.getSessionDynFlags
        let noop_log _ _ _ _ = return ()
            expr = "show " ++ showSDoc (ppr name)
        GHC.setSessionDynFlags dflags{log_action=noop_log}
        mb_txt <- GHC.compileExpr expr
        -- case mb_txt of
        txt <- unsafeCoerce mb_txt
        return $ Just txt
        --    _  -> return Nothing
        -- `finally`
        --   GHC.setSessionDynFlags cms dflags

-}

aztest = do
  let
    args = "./testing/simplifyExpr/SimpleIn1.hs"
    modName = "SimpleIn1"
    closure_call = "f_1 []"
  x <- runInterpreter (runEvalHint args modName closure_call)
  -- 
  case x of
     Left err -> printInterpreterError err
     Right x -> do putStrLn $ show (x)
                   writeFile evaluate_result x


-- ---------------------------------------------------------------------

ghcEvalExpr
  :: (Monad (t m), MonadTrans t, AbstractIO.StdIO m,
      AbstractIO.FileIO m) =>
     String -> String -> String -> t m [Char]
ghcEvalExpr x y z = do
                       lift $ AbstractIO.putStrLn $ ("RefacSimplify.ghcEvalExpr:" ++ show ([x,y,z])) -- ++AZ++ 
                       let res = unsafePerformIO $ rawSystem LocalSettings.evaluate [x,y,z] --   :: String -> [String] -> IO ExitCode
                       lift $ AbstractIO.putStrLn $ show res
                       res2 <- lift $ AbstractIO.readFile evaluate_result
                       case res of
                         (ExitFailure _) -> do
                                               error "The simplification could not be performed, some of the formals to the highlighted expression may not be well-defined."
                                               return "-1"
                         -- ++AZ++ _  -> do --lift $ AbstractIO.putStrLn $ show res2
                         _  -> do lift $ AbstractIO.putStrLn $ show res2
                                  return res2

