module PrettyEnv where

newtype DocM a = DocM (PPHsMode -> a)

instance Functor DocM where fmap f (DocM d) = DocM (f.d)

instance Monad DocM where
  return = DocM . const
  DocM d1>>=xd2 = DocM $ \ e -> let DocM d2 = xd2 (d1 e) in d2 e

runEnv = flip unDocM
unDocM (DocM f) = f
getPPEnv = DocM id

-- Layout environment to pass around

data PPLayout
    = PPOffsideRule  -- classical layout
    | PPSemiColon    -- classical layout made explicit: { d ;
		     --					  d ;
		     --					  d }
    | PPUtrecht      -- Utrecht-style explicit layout:  { d
		     --					; d
		     --					; d
		     --					}
    | PPInLine	     -- inline decls, \n between them 
    | PPNoLayout     -- everything on a single line
      deriving (Eq,Show,Read)

type Indent = Int

data PPHsMode
  = PPHsMode { classIndent,            -- class, instance indent level
	       doIndent,               -- do notation indent level
	       doElseIndent,           -- else inside do indent level
	       caseIndent,             -- case expression indent level
	       letIndent,              -- let indent level
	       funIndent,              -- function defn indent level
	       dataIndent :: Indent,   -- data and type indent level
	       spacing    :: Bool,     -- blank lines between statements?
	       layoutType :: PPLayout, -- to do
	       comments   :: Bool,     -- to come later
	       insideDo   :: Bool,     -- to enable correct printing of
				       -- if-then-else inside a do
--	       insideApp  :: Bool,     -- to enable correct printing of
--				       -- type applications
	       infixParens :: Bool,    -- print parens for infix operators
	       debugInfo   :: Bool,    -- print extra debugging info
	       typeInfo    :: Bool,    -- print extra type info
	       useUnicode  :: Bool     -- ok to use of Unicode characters
	     }

defaultMode = PPHsMode { classIndent  = 4,
			 doIndent     = 3,
			 doElseIndent = 2,
			 caseIndent   = 4,
			 letIndent    = 4,
			 funIndent    = 4,
			 dataIndent   = 4,
			 spacing      = True,
			 layoutType   = PPOffsideRule, 
			 comments     = True,
			 insideDo     = False,
--			 insideApp    = False,
			 infixParens  = True,
			 debugInfo    = False,
			 typeInfo     = True,
			 useUnicode   = False
		       }
