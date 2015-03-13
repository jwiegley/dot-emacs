-- Programatica Front-End Commands, level 1
module Pfe1Cmds where
import Prelude hiding (putStr,putStrLn,print)
import Pfe0Cmds(pfe0Cmds,runPFE0Cmds)
import PfeParse(moduleArg,fileArg,filename,( #@ ), (<@),kwOption)
import PFE0(pput,lex0SourceFile,preparseSourceFile,findFile)

import DefinedNames
import FreeNames
import HsTokens
import HsLexerPass1(lexerPass1Only)
import HsLexMerge(mergeLex)

import PrettyPrint
import AbstractIO
import MUtils
import Data.Maybe(mapMaybe)
import PPModules() -- for PFE

pfe1 ext = runPFE0Cmds ext pfe1Cmds

pfe1Cmds =
     pfe0Cmds ++
     [-- Simple, local module queries
      ("defined" , (moduleArg defined,"list entities defined in the module")),
      ("free"    , (moduleArg free,"list names referenced but not defined in the module")),
      ("pragmas",  (moduleArg pragmas,"extract pragmas from modules")),
      ("lex",      (lFileArg tstlex ,"show the result of lexical analysis")),
      ("lexl",     (lFileArg tstlexl,"show the result of lexical analysis + layout preprocessing")),
      ("preparse", (fileArg preparse,"preparse and show abstract syntax"))
     ]

--- Simple module queries ------------------------------------------------------

free = simple freeNames
defined = simple definedNames
preparse = print @@ preparseSourceFile

simple f = pput.vcat.f @@ preparseSourceFile @@ findFile

pragmas = putStr.unlines.map show.lex2pragmas.snd @@ lex0SourceFile @@ findFile

tstlex  one = printLex one . mergeLex @@ lex0SourceFile
tstlexl one = printLex one . lexerPass1Only . mergeLex @@ lex0SourceFile

printLex True = putStrLn . unlines . map show
printLex False = print

lFileArg f = f #@ kwOption "-1" <@ filename

lex2pragmas = mapMaybe pragma
  where
    pragma (NestedComment,(p,'{':'-':'#':s)) | last3 s=="#-}" =
      Just (p,droplast3 s)
    pragma _ = Nothing

    last3 = reverse . take 3 . reverse
    droplast3 = reverse . drop 3 . reverse
