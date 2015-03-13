module HsTokens where

-- Haskell token classifications:

data Token
  = Varid | Conid | Varsym | Consym
  | Reservedid | Reservedop  | Specialid
  | IntLit | FloatLit | CharLit | StringLit
  | Qvarid | Qconid | Qvarsym | Qconsym
  | Special | Whitespace

  | NestedCommentStart -- will cause a call to an external function
  | NestedComment  -- from the external function
  | LiterateComment -- not handled by the lexer

  | Commentstart  -- dashes
  | Comment -- what follows the dashes

  | ErrorToken | GotEOF | TheRest

  | ModuleName | ModuleAlias -- recognized in a later pass

  -- Inserted during layout processing (see Haskell 98, 9.3):
  | Layout     -- for implicit braces
  | Indent Int -- <n>, to preceed first token on each line
  | Open Int   -- {n}, after let, where, do or of, if not followed by a "{"
  deriving (Show,Eq,Ord)
