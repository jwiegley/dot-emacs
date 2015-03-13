import System(getArgs)
import Unlit(readHaskellFile)
import L(l)
import HsLexerPass1
import HsLayoutPre(layoutPre)
import List(partition)

-- This version reads the Haskell input from files named on the command line.
main = mapM_ doLayout =<< getArgs

doLayout path = putStrLn . layout =<< readHaskellFile path

layout =
    concatMap tokenString . 
    uncurry (mergeBy (cmpBy tokenPos)) .
    apFst (flip l [] . layoutPre) .
    partition (notWhite.fst) .
    lexerPass0
  where
    tokenPos = fst . snd
    tokenString = snd . snd


--- Utilities

apFst f (x,y) = (f x,y)
cmpBy f x y      = f x `compare` f y

mergeBy cmp [] ys  = ys
mergeBy cmp xs []  = xs
mergeBy cmp a@(x:xs) b@(y:ys) =
    case x `cmp` y of
      GT -> y : mergeBy cmp a ys 
      _ -> x : mergeBy cmp xs b
