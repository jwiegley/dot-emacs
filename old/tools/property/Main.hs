-- $Id: Main.hs,v 1.14 2001/10/10 23:36:06 hallgren Exp $

-- Currently a test harness for the lexer/parser/pretty printer.

--ToDo: Are initial values for SrcLoc/current column correct?

module Main (main) where


import IO
import Lexer
import ParseMonad
import PropParser
import ParseUtil
import Syntax
import PrettyPrint
import System
import GetOpt
import IOExts
import List
import Rewrite(rewriteModule)
import HsAssocInitEnv(initEnv)
import CommandLine
import Compile
import Monad
import MUtils(( # ))

main :: IO ()
main = case commandLine of
         (flags, args, [])    ->
           do (file, inp) <- case args of
			     []  -> do inp <- getContents
				       return ("stdio", inp)
			     [f] -> do inp <- readFile f
				       return (f, inp)
			     _   -> error $ usageInfo usage options
              case handleFlag (getFlag flags) file inp of
                Good output          -> putStrLn output
                CompileError message ->
                    error $ "Compilation had errors:\n\n" ++ message
         (    _,   _, errors) ->
             error $ concat errors ++ usageInfo usage options


handleFlag :: Flag -> FilePath -> String -> Compile String
handleFlag ParseInternal f s    = liftM show $ parseModule f s
handleFlag (ParsePretty lo) f s = liftM (renderWithMode
                                            defaultMode { layoutType = lo } .
                                         ppi)
                                  (parseModule f s)
handleFlag ToHaskell f s        = liftM pp $ parseModule f s
handleFlag StaticAnalysis f s   = compileError
                                  "progc: static analysis not yet implemented"
handleFlag TypeCheck f s        = compileError
                                  "progc: type checking not yet implemented"
handleFlag Help f s             = return $
                                  usageInfo ("The Programatica Compiler\n" ++
                                             usage)
                                  options

parseModule :: FilePath -> String -> Compile HsModuleR
parseModule f s =  rewriteModule initEnv # parseFile parse f s
