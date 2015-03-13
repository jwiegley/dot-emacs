{-
This program converts Haskell source to HTML. Apart from the Haskell source
files, it requires the cross reference information produced by running

       tstModules xrefs <files>

on the complete program.
-}

import HsLexerPass1
import System(getArgs)
import Unlit(readHaskellFile)
import MUtils
import RefsTypes
import HLex2html
import PathUtils(normf)

-- fix the hard coded path?
main =
  do args <- getArgs
     fms <- mapFst normf # (readIO =<< readFile "hi/ModuleSourceFiles.hv")
     case args of
       ["file",m]   -> putStrLn . maybe "?" id . lookup m . map swap $ fms
       ["html",m]   -> module2html m fms
       ["f2html",f] -> file2html (normf f) fms
       ["all2html"] -> all2html fms
       ["modules"]  -> putStr . unlines . map (\(f,m)->m++" "++f) $ fms
       ["files"]  -> putStr . unlines . map fst $ fms
       _ -> fail "Usage: hs2html (file <module> | html <module> | f2html <file> | files | modules | all2html)"

readl s = map read . lines $ s

readModule = readRefs >#< lexHaskellFile
readRefs :: Module -> IO Refs
readRefs m = readl # readFile ("hi/"++m++".refs")
lexHaskellFile f = lexerPass0 # readHaskellFile Nothing f

all2html fms = mapM_ one2html fms
  where
    one2html (f,m) = writeFile h.hlex2html (f,fms)=<<readModule (m,f)
      where h = "hi/"++m++".html"

module2html m fms =
  case [f|(f,m')<-fms,m'==m] of
    f:_ -> haskell2html (f, fms) (m, f)
    _ -> fail "Unknown module"

file2html f fms =
  case [m|(f',m)<-fms,f'==f] of
    m:_ -> haskell2html (f, fms) (m,f)
    _ -> fail "Unknown source file"

haskell2html ffm mf = putStrLn.hlex2html ffm=<<readModule mf
