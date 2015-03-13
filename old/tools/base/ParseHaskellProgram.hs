module ParseHaskellProgram where
import ParseProgram(parseProgram)
import HsParser(parse)
import DefinedNamesBase() -- instances
import ReAssocBase()      -- instances
import ParsedSyntax(HsModuleR,ModuleName,Id,HsName)
import WorkModule(WorkModuleI)

{-+
This is a function to parse a plain Haskell program. Given a list of files
containing the modules of a Haskell program, it returns a list of strongly
connected components of modules, and an association list giving information
for each module what is in scope and what is exported.
-}
parseHaskellProgram:: 
    [FilePath] -> IO ([[HsModuleR]], [(ModuleName, WorkModuleI HsName Id)])
parseHaskellProgram = parseProgram parse

{-+
The function is constructed from the reusable function parseProgram,
which takes a module parser as an argument. This allows it to be used
for variants of Haskell, e.g. where there are new forms of
declarations or expressions. For this to work, there must be instances
in some classes for the type of declarations.  See the module
ParseProgram for details.
-}
