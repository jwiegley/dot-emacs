module Util.Args.ArgDescr ( DefaultValue(..)
                          , ArgDescr(..)
                          , KnownArgs
                          ) where

-- default value for cli option
data DefaultValue = ConstValue String -- explicit default value
                  | DynValue String   -- human readable description of a process
                                      -- that will provide default value

-- cli option description
data ArgDescr =
      -- switch
      SwitchDescr { argName  :: String     -- switch name (e.g. 'verbose' for --verbose)
                  , helpMsg  :: String     -- human readable description of this switch
                  , shortOpt :: Maybe Char -- optional short version for this switch
                                          -- (e.g. 'v' for '-v'
                                          -- as a shortcut for '--verbose')
                  }
    -- option with a value
  | ValArg { argName      :: String -- option name (e.g. 'key' for '--key=value')
           , valTemplate  :: String -- help template for value (e.g. 'PATH' for --binary=PATH)
           , defaultValue :: DefaultValue -- default value
           , helpMsg      :: String -- human readable description of this switch
           }

type KnownArgs = [ArgDescr]
