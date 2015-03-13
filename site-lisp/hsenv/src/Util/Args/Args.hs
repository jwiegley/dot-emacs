{-# LANGUAGE Arrows #-}
module Util.Args.Args (parseArgs) where

import Util.Args.ArgDescr (ArgDescr(..), KnownArgs)
import Util.Args.ArgArrow (ArgArrow, runArgArrow, askArgs, getKnownArgs, addKnownArg)
import Util.Args.RawArgs (Args(..), parseArguments)
import Control.Arrow ((>>>), returnA, arr)
import System.Environment (getArgs)
import System.IO (stderr, hPutStrLn)
import System.Exit (exitFailure, exitSuccess)
import Data.Maybe (catMaybes)
import Util.Args.Usage (usage)

-- cli arg parsing result
data ArgParseResult a = Usage
                      | Help
                      | Error String
                      | Version
                      | OK a

-- wraps a cli arg parsing computation to add few standard
-- arguments: --help (and -h) and --version
-- and allows to distinguish them in the result
helperArgArrow :: ArgArrow a b -> ArgArrow a (ArgParseResult b)
helperArgArrow arrow = proc x -> do
  addKnownArg knargs -< ()
  args <- askArgs -< ()
  if "help" `elem` switches args || 'h' `elem` shortSwitches args then
    returnA -< Help
   else if "usage" `elem` switches args then
    returnA -< Usage
   else if "version" `elem` switches args then
    returnA -< Version
   else
    arrow >>> arr OK -< x
    where knargs = [versionOpt, helpOpt]
          helpOpt = SwitchDescr "help" "Show this help message" (Just 'h')
          versionOpt = SwitchDescr "version" "Show version string" Nothing

-- prints a msg to stderr and exits program with return value 1
failWith :: String -> IO a
failWith s = hPutStrLn stderr s >> exitFailure

-- validates provided cli arguments against known argument descriptions
-- handles unknown arguments, and currently forbids positional arguments
validateArguments :: Args -> KnownArgs -> IO ()
validateArguments args knArgs
    | not $ null $ positionals args = failWith "Positional arguments are not allowed"
    | otherwise =
        either failWith return $ do
          mapM_ (validate "short switch" "-" knShortSwitches (:"")) $ shortSwitches args
          mapM_ (validate "switch" "--" knSwitches id) $ switches args
          mapM_ (validate "option" "--" knKeys id . fst) $ valArgs args
    where knShortSwitches = catMaybes $ flip map knArgs $ \x -> case x of
                               SwitchDescr _ _ c -> c
                               _ -> Nothing
          knSwitches = catMaybes $ flip map knArgs $ \x -> case x of
                               SwitchDescr name _ _ -> Just name
                               _ -> Nothing
          knKeys = catMaybes $ flip map knArgs $ \x -> case x of
                               ValArg name _ _ _ -> Just name
                               _ -> Nothing
          validate xName prefix knownXs showX x =
              if x `elem` knownXs then
                  Right ()
              else
                  Left $ "Unknown " ++ xName ++ " '" ++ prefix ++ showX x ++ "'"

-- takes a cli arg parsing computation, version string and usage msg footer
-- runs the computation on program cli arguments
-- and returns the result. if arguments validation fails,
-- prints usage message and exits with failure
parseArgs :: ArgArrow () a -> String -> String -> IO a
parseArgs arrgArr version outro = do
  args <- getArgs
  case parseArguments args of
    Left s -> failWith s
    Right parsedArgs -> do
      validateArguments parsedArgs $ getKnownArgs arrgArr'
      result <- runArgArrow arrgArr' parsedArgs
      case result of
        OK a -> return a
        Error s -> failWith s
        Version -> putStrLn version >> exitSuccess
        _ -> usage arrgArr' outro >>= putStr >> exitSuccess
  where arrgArr' = helperArgArrow arrgArr
