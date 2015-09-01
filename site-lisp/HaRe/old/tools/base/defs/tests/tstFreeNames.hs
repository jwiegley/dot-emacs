import HsParser(parse)
import ParseProgram(parseProgram)
import FreeNames
import FreeNamesBase
import HsModule (hsModDecls)
import PrettyPrint
import ReAssocBase

import System(getArgs)


test fs = do
    (scMods, wms) <- parseProgram parse fs
    mapM_ f (concat scMods)

    where
    f = mapM_ g . hsModDecls 
    g d = do
        putStrLn (pp d)
        putStrLn (pp (fst `map` freeNames d))
        putStrLn ""

main = do
    as <- getArgs
    test as    

