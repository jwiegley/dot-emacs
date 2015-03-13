module ParseAttrs(module ParseAttrs,module Attrs) where
import Char(isSpace)
import FileUtils(readFileNow)
import MUtils

import Attrs

{-
Read an attribute file.

 Attribute files use a textual file format for association lists.
 Each line in an attribute file may specify a binding of a tag
 string to a value string using a single colon to separate the
 two.  If the colon is omitted, then a value of "" is assumed.
 Leading whitespace at the beginning of each line and preceding
 the value (i.e., after the first, if any, colon) is ignored.
 Lines containing only whitespace, or in which the first
 non-whitespace character is a '#' are treated as comments.
 (Despite this, we do not intend attribute files to be a
 human-readable format under normal circumstances.)
--
 Here is a sample attribute file:
--
 # This is a comment
 
 foo: your name here!
 date:today
 
 # here is a line with no value ...
 set filec
 
 foo:bar
 # if the same tag is used more than once, then
 # we simply get multiple attribute values with
 # the same tag.
 
-}

--readAttrs  :: FilePath -> IO Attrs
readAttrs path = parseAttrs # readFileNow path

type Line  = String

parseAttrs = map readAttr . filter (not . comment) . map trim . lines
    where 
	  trim           :: Line -> Line
	  trim            = dropWhile isSpace

	  comment        :: Line -> Bool
	  comment l       = null l || (head l == '#')

	  readAttr       :: String -> Attr
	  readAttr l      = case span (':'/=) l of
			      (tag, (c:val)) -> (tag, trim val)
			      prop           -> prop

{-+
certFiles returns the list of files found in an attribute set.
-}
certFiles attrs = [path|(name,path)<-attrs,namesFile name]
