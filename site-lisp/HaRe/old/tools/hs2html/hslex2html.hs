import System(getArgs)
import HsLexerPass1(lexerPass0)
import HLex2html(simpleHlex2html)
import Unlit(readHaskellFile)

main =
  do args <- getArgs
     if null args
       then interact hslex2html
       else mapM_ hsfile2html args

hsfile2html path = putStr . hslex2html =<< readHaskellFile Nothing path

hslex2html = simpleHlex2html.lexerPass0
