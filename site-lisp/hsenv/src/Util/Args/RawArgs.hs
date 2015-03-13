module Util.Args.RawArgs ( Args(..)
                         , parseArguments
                         ) where

import Data.Monoid (Monoid(..))
import Control.Monad (liftM)
import Control.Monad.Instances ()
import Util.List (breakOn)

{-# ANN Args "HLint: ignore Use String" #-}
-- parsed command line options
data Args = Args { shortSwitches :: [Char]             -- list of enabled short switches
                 , switches      :: [String]           -- list of enabled switches
                 , valArgs       :: [(String, String)] -- list of (key,value) cli opts
                 , positionals   :: [String]           -- positional arguments
                 }

instance Monoid Args where
    mempty = Args [] [] [] []
    Args xs1 ys1 zs1 us1 `mappend` Args xs2 ys2 zs2 us2 =
        Args (xs1 ++ xs2) (ys1 ++ ys2) (zs1 ++ zs2) (us1 ++ us2)

-- parses a single word or returns an error
parseArgument :: String -> Either String Args
parseArgument ('-':'-':arg) =
    Right $ case breakOn '=' arg of
      Nothing         -> mempty{switches = [arg]}
      Just (key, val) -> mempty{valArgs = [(key, val)]}
parseArgument ['-', c] = Right mempty{shortSwitches = [c]}
parseArgument param@('-':_) = Left $ "Invalid option: '" ++ param ++ "'"
parseArgument arg = Right mempty{positionals = [arg]}

-- parses many words or returns an error
parseArguments :: [String] -> Either String Args
parseArguments args =
    case breakOn "--" args of
      Nothing -> mconcat `liftM` mapM parseArgument args
      Just (args', rest) -> do
        parsedArgs <- mapM parseArgument args'
        return $ mconcat parsedArgs `mappend` mempty{positionals = rest}
