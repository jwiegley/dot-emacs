module ParserOptions where

data Flags
  = Flags {
      prel::Bool,       -- Should all modules implicitly import Prelude?
      plogic::Bool,     -- Recognize extra keywords for Plogic?
      cpp::Maybe String -- Should the C preprocessor be used?
    }
    deriving (Eq,Show,Read)

flags0 = Flags True True Nothing
cpp1= "/lib/cpp -traditional -P -D__HASKELL98__ -D__PFE__"

parserOptions flags args =
  case args of
    "noprelude":args         -> parserOptions flags{prel=False   } args
    "prelude"  :args         -> parserOptions flags{prel=True    } args
    "noplogic" :args         -> parserOptions flags{plogic=False } args
    "plogic"   :args         -> parserOptions flags{plogic=True  } args
    "cpp"      :args         -> parserOptions flags{cpp=Just cpp1} args
    ('c':'p':'p':'=':s):args -> parserOptions flags{cpp=Just s   } args
    "nocpp"    :args         -> parserOptions flags{cpp=Nothing  } args
    _                        -> (flags,args)
