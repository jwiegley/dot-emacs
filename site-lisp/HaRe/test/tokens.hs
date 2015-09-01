
import           TestUtils

import SrcLoc
import Panic
import Lexer

main = do
  (t,toks) <- parsedFileGhc "./test/testdata/MoveDef/Md1.hs"
  let s = showRichTokenStream' toks
  putStrLn s
  putStrLn "----------------------------------------"
  putStrLn (show $ filter (\(_,s) -> s == "") toks)


-- Based on version from GHC source

-- | Take a rich token stream such as produced from 'getRichTokenStream' and
-- return source code almost identical to the original code (except for
-- insignificant whitespace.)
showRichTokenStream' :: [(Located Token, String)] -> String
showRichTokenStream' ts = go startLoc ts ""
    where sourceFile = getFile $ map (getLoc . fst) ts
          getFile [] = panic "showRichTokenStream: No source file found"
          getFile (UnhelpfulSpan _ : xs) = getFile xs
          getFile (RealSrcSpan s : _) = srcSpanFile s
          startLoc = mkRealSrcLoc sourceFile 1 1
          go _ [] = id
          go loc ((L span tok, str'):ts)
              = case span of
                UnhelpfulSpan _ -> go loc ts
                RealSrcSpan s
                 | locLine == tokLine -> ((replicate (tokCol - locCol) ' ') ++)
                                       . (str ++)
                                       . go tokEnd ts
                 | otherwise -> ((replicate (tokLine - locLine) '\n') ++)
                              . ((replicate tokCol ' ') ++)
                              . (str ++)
                              . go tokEnd ts
                  where (locLine, locCol) = (srcLocLine loc, srcLocCol loc)
                        (tokLine, tokCol) = (srcSpanStartLine s, srcSpanStartCol s)
                        tokEnd = realSrcSpanEnd s
                        -- mark the position of the hidden tokens
                        str = case str' of
                                "" -> case tok of
                                        ITvocurly -> "*{*"
                                        ITsemi    -> "*;*"
                                        ITvccurly -> "*}*"
                                        _ -> "{|}"
                                _  -> str'
