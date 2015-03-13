import RemovePatBinds
import System (getArgs)
import PrettyPrint
import ParseHaskellProgram

import TiNames(ValueId(..))
import HsConstants(prelude_mod)
import PosSyntax
import MapDeclMBase

main = do
    files <- getArgs
    (modss, wms) <- parseHaskellProgram files 
    putStrLn $ render
             $ vcat 
             $ map (ppi . remPats)
             $ concat modss

apos = SrcLoc "???" 0 0

-- not complete, should probably be somewhere else...
instance ValueId HsName where
    prelVal x = qualid (apos,"Prelude." ++ x)
    localVal x = unqualid (apos,x)

