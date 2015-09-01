-- From nhc13/src/comiler13/Unlit.hs
module Unlit(CommentClass(..),unlit,readHaskellFile,writeHaskellFile, optUnlit,isLiterateFile) where
import Prelude hiding (readFile)
import AbstractIO
import MUtils(apFst,pairWith)

-- Part of the following code is from "Report on the Programming Language Haskell",
-- version 1.2, appendix C.

import Data.Char

readHaskellFile cpp path = optUnlit path =<< cppFile cpp path

writeHaskellFile path code = AbstractIO.writeFile path $ optRelit path code

cppFile Nothing path = readFile path
cppFile (Just cpp) path =
  do let tmpname = "hi/readHaskellFile.cpp.tmp" -- Use a unique name!!!
     ExitSuccess <- system (cpp++" "++path++" >"++tmpname) -- improve error message!
     src <- readFile tmpname
     removeFile tmpname
     return src

optRelit path =
  if isLiterateFile path
  then relit 
  else id

optUnlit path =
  if isLiterateFile path
  then \ s -> let ((litcmnts,code),es) = unlit path s
              in if null es
	         then return (litcmnts,unlines code)
		 else fail (unlines es)
  else \ s -> return ([],s)

isLiterateFile path = last4 path == ".lhs"
  where last4 = reverse . take 4 . reverse

--------------------------------------------------------------------------------

-- basic re-literation hack
-- assume {-+\t starts encoded literate comment
-- assume > for code by default (lines starting with ' '), 
-- begin/end only if code starts in first column
-- (will keep adding empty lines before \begin{code}..)
relit = unlines . inCode False . lines
  where
    inCode False []                = []
    inCode True  []                = ["\\end{code}"]
    inCode False (x:xs) 
               | take 4 x=="{-+\t" = (drop 4 x):(inComment xs)
    inCode True  (x:xs) 
               | take 4 x=="{-+\t" = "\\end{code}":((drop 4 x):(inComment xs))
    inCode False (x:xs) | x=="{-+" = "":(inComment xs)
    inCode True  (x:xs) | x=="{-+" = "\\end{code}":("":(inComment xs))
    inCode True  (x:xs)            = x:(inCode True xs)
    inCode False (x:xs) 
               | all isSpace x     = x:(inCode False xs)
    inCode False ((' ':x):xs)      = ('>':x):(inCode False xs)
    inCode False (('#':x):xs)      = ('#':x):(inCode False xs)
    inCode False xs@(_:_)          = "\\begin{code}":(inCode True xs)

    inComment []               = []
    inComment (x:xs) | x=="-}" = "":(inCode False xs)
    inComment (x:xs)           = x:(inComment xs)

--------------------------------------------------------------------------------

--unlit :: String -> String -> String
unlit file =
--apFst new_unclassify .        -- put literate text in nested comments
  apFst (unzip . map unclassify1) . -- return comment text and code separately
  pairWith (adjacent (Blank "") . addpos file 0) . -- error checking
  classify .
  lines
--------------------------------------------------------------------------------

data Classified
  = Program String String
  | Blank String
  | Comment String
  | Include Int String
  | Pre String

classify :: [String] -> [Classified]
classify []                = []
classify (l@('\\':x):xs) | x == "begin{code}" = Blank l : allProg xs
   where allProg [] = []  -- Should give an error message, but I have no good position information.
         allProg (l@('\\':x):xs) |  x == "end{code}" = Blank l : classify xs
	 allProg (x:xs) = Program "" x:allProg xs
classify (('>':x):xs)      = Program ">" (' ':x) : classify xs
classify (('!':x):xs)      = Program "!" (' ':x) : classify xs -- Programatica extra
classify (('#':x):xs)      = (case words x of
                                (line:file:_) | all isDigit line -> Include (read line) file
                                _                                -> Pre x
                             ) : classify xs
classify (x:xs) | all isSpace x = Blank x:classify xs
classify (x:xs)                 = Comment x:classify xs

-- Old version: put literate comment lines in one-line comments
--old_unclassify = unlines . map unclassify1

data CommentClass = CodePrefix | Directive | BlankLine | LitCmnt

unclassify1 :: Classified -> ((CommentClass,String),String)
unclassify1 (Program cmnt code) = ((CodePrefix,cmnt),code)
unclassify1 (Pre s)             = ((Directive,'#':s),"")
unclassify1 (Include i f)       = ((Directive,'#':' ':show i ++ ' ':f),"")
unclassify1 (Blank cmnt)        = ((BlankLine,cmnt),"")
unclassify1 (Comment cmnt)      = ((LitCmnt,cmnt),"")

-- New version: put literate comment blocks in nested comments
-- (Drawback: these can potentially interfere with other comments)
new_unclassify = unclassify0
  where
    unclassify0 (Comment s:xs) = "{-+\t"++s++"\n"++unc xs -- -}
    unclassify0 xs = un xs

    -- Normal state, inside code block
    un [] = []
    un (Blank cmnt:Comment s:xs) = "{-+"++cmnt++"\n"++s++"\n"++unc xs -- -}
    un (x:xs) = snd (unclassify1 x)++"\n"++un xs -- ??

    -- Comment state, inside a literate comment
    unc [] = "-}\n"
    unc (Comment s:xs) = s++"\n"++unc xs
    unc (Blank s:xs) = s++"\n"++unb xs -- ??

    -- Blank line state, inside a literate comment, after a blank line
    unb [] = "-}\n"
    unb (Blank s:xs) = s++"\n"++unb xs -- ??
    unb xs@(Comment _:_) = "\n"++unc xs
    unb xs = "-}\n"++un xs

--adjacent :: Classified -> [((FilePath,Int),Classified)] -> [String]
adjacent _ [] = []
adjacent y ((pos,x):xs) =
  case (y,x) of
   (_        , Pre _      ) -> adjacent y xs
   (_        , Include _ _) -> adjacent y xs
   (Program _ _, Comment _) -> message pos "program" "comment":adjacent x xs
   (Comment _, Program _ _) -> message pos "comment" "program":adjacent x xs
   _                        -> adjacent x xs

addpos file n [] = []
addpos file n (x:xs) =
    case x of
      Include i f -> l:addpos f i xs
      _ -> l:addpos file (n+1) xs
  where l = ((file,n),x)

message pos p c = showpos pos++": "++p++ " line before "++c++" line.\n"
  where
    showpos ([],n)     = "Line "++show n
    showpos ("\"\"",n) = "Line "++show n
    showpos (file,n)   = "In file " ++ file ++ " at line "++show n
