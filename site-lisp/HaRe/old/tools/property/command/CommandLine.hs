-- $Id: CommandLine.hs,v 1.2 2002/05/18 20:40:57 hallgren Exp $

module CommandLine where

import System
import GetOpt
import IOExts
import PrettyPrint


data Flag = ParseInternal          -- print abstract syntax in internal format
          | ParsePretty PPLayout   -- pretty print in given style
          | ToHaskell              -- forgetful functor from Programatica
          | StaticAnalysis         -- run static analysis
          | TypeCheck              -- run type checker
          | Help                   -- give short usage info
            deriving Eq

options =
   [ Option []        ["ast", "abstract-syntax-tree"]
         (NoArg ParseInternal)
         "print abstract syntax in internal format",
     Option []        ["pretty"]
         (OptArg style "STYLE")
         "pretty print in STYLE[(o)ffside|(s)emicolon|(u)trecht|(i)nline|(n)one] (default = offside)",
     Option []        ["hs", "haskell"]
         (NoArg ToHaskell)
         "produce Haskell code with Programatica constructs commented out",
     Option []        ["sa", "static", "static-analysis"]
         (NoArg StaticAnalysis) 
         "run static analysis",
     Option []        ["tc", "typecheck"]
         (NoArg TypeCheck)
         "run typechecker",
     Option ['h','?'] ["help"]      
         (NoArg Help)
         "display this help message and exit"
   ]

style :: Maybe String -> Flag
style Nothing  = ParsePretty PPOffsideRule
style (Just s) = ParsePretty $
         case s of
         "o"         -> PPOffsideRule
         "offside"   -> PPOffsideRule
         "s"         -> PPSemiColon
         "semicolon" -> PPSemiColon
         "u"         -> PPUtrecht
         "utrecht  " -> PPUtrecht
         "i"         -> PPInLine
         "inline"    -> PPInLine
         "n"         -> PPNoLayout
         "none"      -> PPNoLayout
         _           -> PPOffsideRule

getFlag :: [Flag] -> Flag
getFlag []  = ParsePretty PPOffsideRule
getFlag [f] = f
getFlag _   = error usage

usage = "usage: pgc [option] [filename]"

commandLine = getOpt Permute options $ unsafePerformIO getArgs
