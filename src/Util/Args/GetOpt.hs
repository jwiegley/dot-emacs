{-# LANGUAGE MultiParamTypeClasses
  , FunctionalDependencies
  , TypeSynonymInstances
  , FlexibleInstances
  , Arrows
  #-}
module Util.Args.GetOpt ( GetOpt(..)
                        , Switch(..)
                        , DynOpt(..)
                        , StaticOpt(..)
                        ) where

import Util.Args.ArgArrow (ArgArrow, askArgs, addKnownArg)
import Util.Args.ArgDescr (DefaultValue(..), ArgDescr(..))
import Util.Args.RawArgs (Args(..))
import Data.Maybe (fromMaybe)
import Control.Arrow (returnA)

-- getOpt method takes a cli option description and returns at runtime value for that option.
-- it also statically records information about such option (and uses it to generate usage)
class GetOpt a b | a -> b where
    getOpt :: a -> ArgArrow () b

-- description of a cli switch, getOpt-ing it will return True if it's present
-- in cli args and False otherwise
data Switch =
    Switch { switchName  :: String     -- switch long name (e.g. 'verbose' for '--verbose')
           , switchHelp  :: String     -- human readable switch description (used for usage msg)
           , switchShort :: Maybe Char -- optional short version of this switch
                                      -- (e.g. 'v' for '-v')
           }

instance GetOpt Switch Bool where
    getOpt descr = proc () -> do
      addKnownArg [SwitchDescr (switchName descr)
                               (switchHelp descr)
                               (switchShort descr)] -< ()
      args <- askArgs -< ()
      let longSwitchStatus = switchName descr `elem` switches args
          switchStatus = case switchShort descr of
                           Nothing -> longSwitchStatus
                           Just c  -> longSwitchStatus || c `elem` shortSwitches args
      returnA -< switchStatus

-- description of a key,value cli argument, that if not present,
-- defaults to a value returned by some dynamic process
-- getOpt-ing it will return Just its value if it's present in cli args,
-- otherwise Nothing
data DynOpt =
    DynOpt { dynOptName        :: String -- key name (e.g. 'foo' for '--foo=bar')
           , dynOptTemplate    :: String -- help template for value
                                        -- (e.g. 'PATH' for --binary=PATH)
           , dynOptDescription :: String -- human readable description of a process
                                        -- that will provide default value
                                        -- (e.g. 'current directory')
           , dynOptHelp        :: String -- human readable switch description
                                        -- (used for usage msg)
           }

instance GetOpt DynOpt (Maybe String) where
    getOpt descr = proc () -> do
      addKnownArg [ValArg (dynOptName descr)
                          (dynOptTemplate descr)
                          (DynValue $ dynOptDescription descr)
                          (dynOptHelp descr)] -< ()
      args <- askArgs -< ()
      returnA -< lookup (dynOptName descr) $ valArgs args

-- description of a key,value cli argument, that if not present,
-- defaults to an explicit value
-- getOpt-ing it will return String with its value if it's present in cli args,
-- otherwise default value is returned
data StaticOpt =
    StaticOpt { staticOptName     :: String -- key name (e.g. 'foo' for '--foo=bar')
              , staticOptTemplate :: String -- help template for value
                                           -- (e.g. 'PATH' for --binary=PATH)
              , staticOptDefault  :: String -- default value for this argument
              , staticOptHelp     :: String -- human readable switch description
                                           -- (used for usage msg)
              }

instance GetOpt StaticOpt String where
    getOpt descr = proc () -> do
      addKnownArg [ValArg (staticOptName descr)
                          (staticOptTemplate descr)
                          (DynValue $ staticOptDefault descr)
                          (staticOptHelp descr)] -< ()
      args <- askArgs -< ()
      returnA -< fromMaybe (staticOptDefault descr)
                          $ lookup (staticOptName descr)
                          $ valArgs args
