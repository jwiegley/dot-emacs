module UTF8Util where
import System.IO.Error(isUserError,ioeGetErrorString)
import UTF8

utf8 = encodeUTF8 -- . arrows

{-
-- Convert \ and -> into lambda and arrow
arrows ('-':'>':s) = '\x2192':arrows s
arrows ('\\':' ':s) = '\x03bb':' ':arrows s
arrows (c:cs) = c:arrows cs
arrows [] = []
-}

-- Smileys
happy = ['\x263a']
sad = ['\x2639'] 
-- Note: GHC <=5.02.2 silently truncates Unicode characters in string literals

-- Encode error output
utf8err e =
  if isUserError e
  then fail (utf8 (ioeGetErrorString e++"\n"++sad))
  else ioError e


