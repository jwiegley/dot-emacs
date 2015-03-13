-- From nhc13/src/comiler13/Unlit.hs
module Unlit(unlit,readHaskellFile,optUnlit,isLiterateFile) where

-- Part of the following code is from "Report on the Programming Language Haskell",
-- version 1.2, appendix C.

import Char

readHaskellFile path = fmap (optUnlit path) (readFile path)

optUnlit path =
  if isLiterateFile path
  then unlit path
  else id

isLiterateFile path = last4 path == ".lhs"
  where last4 = reverse . take 4 . reverse

--------------------------------------------------------------------------------

data Classified = Program String | Blank | Comment String | Include Int String | Pre String

classify :: [String] -> [Classified]
classify []                = []
classify (('\\':x):xs) | x == "begin{code}" = Blank : allProg xs
   where allProg [] = []  -- Should give an error message, but I have no good position information.
         allProg (('\\':x):xs) |  x == "end{code}" = Blank : classify xs
	 allProg (x:xs) = Program x:allProg xs
classify (('>':x):xs)      = Program (' ':x) : classify xs
classify (('#':x):xs)      = (case words x of
                                (line:file:_) | all isDigit line -> Include (read line) file
                                _                                -> Pre x
                             ) : classify xs
classify (x:xs) | all isSpace x = Blank:classify xs
classify (x:xs)                 = Comment x:classify xs

-- Old version: put literate comment lines in one-line comments
old_unclassify = unlines . map unclassify1

unclassify1 :: Classified -> String
unclassify1 (Program s) = s
unclassify1 (Pre s)     = '#':s
unclassify1 (Include i f) = '#':' ':show i ++ ' ':f
unclassify1 Blank       = ""
unclassify1 (Comment s) = "-- "++s

-- New version: put literate comment blocks in nested comments
-- (Drawback: these can potentially interfere with other comments)
new_unclassify = unclassify0
  where
    unclassify0 (Comment s:xs) = "{-+\t"++s++"\n"++unc xs -- -}
    unclassify0 xs = un xs

    -- Normal state, inside code block
    un [] = []
    un (Blank:Comment s:xs) = "{-+\n"++s++"\n"++unc xs -- -}
    un (x:xs) = unclassify1 x++"\n"++un xs

    -- Comment state, inside a literate comment
    unc [] = "-}\n"
    unc (Comment s:xs) = s++"\n"++unc xs
    unc (Blank:xs) = unb xs

    -- Blank line state, inside a literate comment, after a blank line
    unb [] = "-}\n"
    unb (Blank:xs) = "\n"++unb xs
    unb xs@(Comment _:_) = "\n"++unc xs
    unb xs = "-}\n"++un xs

unlit :: String -> String -> String
unlit file =
  new_unclassify . adjecent file (0::Int) Blank . classify . lines

adjecent :: String -> Int -> Classified -> [Classified] -> [Classified]
adjecent file 0 _             (x              :xs) = x : adjecent file 1 x xs -- force evaluation of line number
adjecent file n y@(Program _) (x@(Comment _)  :xs) = error (message file n "program" "comment")
adjecent file n y@(Program _) (x@(Include i f):xs) = x: adjecent f    i     y xs
adjecent file n y@(Program _) (x@(Pre _)      :xs) = x: adjecent file (n+1) y xs
adjecent file n y@(Comment _) (x@(Program _)  :xs) = error (message file n "comment" "program")
adjecent file n y@(Comment _) (x@(Include i f):xs) = x: adjecent f    i     y xs
adjecent file n y@(Comment _) (x@(Pre _)      :xs) = x: adjecent file (n+1) y xs
adjecent file n y@Blank       (x@(Include i f):xs) = x: adjecent f    i     y xs
adjecent file n y@Blank       (x@(Pre _)      :xs) = x: adjecent file (n+1) y xs
adjecent file n _             (x@next         :xs) = x: adjecent file (n+1) x xs
adjecent file n _             []                    = []

message "\"\"" n p c = "Line "++show n++": "++p++ " line before "++c++" line.\n"
message []     n p c = "Line "++show n++": "++p++ " line before "++c++" line.\n"
message file   n p c = "In file " ++ file ++ " at line "++show n++": "++p++ " line before "++c++" line.\n"
