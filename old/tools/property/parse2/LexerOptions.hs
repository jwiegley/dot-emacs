module LexerOptions where

data LexerFlags = Flags { plogic :: Bool } deriving (Eq,Read,Show)

lexerflags0 = Flags True

lexerOptions flags args =
  case args of
    "noplogic":args -> lexerOptions flags{plogic=False } args
    "plogic"  :args -> lexerOptions flags{plogic=True  } args
    _               -> (flags,args)
