{-+
Compiling regular expressions, the new way.
-}
module CompileRegExp where
import RegExpOps
import qualified Data.Map as M
import Maybe(isJust,fromJust)
--import Trace

compile r = number (build M.empty [r])
  where
    build dfa [] = []
    build dfa (r:rs) =
       if isJust (M.lookup r dfa)
       then build dfa rs
       else (r,fs):build dfa' (frs++rs)
     where
       dfa' = M.insert r fs dfa
       fs = factors r
       frs = map snd (snd fs)

    number states = map numb states
      where
        mapping = M.fromList (zip (map fst states) [(1::Int) ..])
	num = fromJust . (\k -> M.lookup k mapping)

        numb (r,(b,edges)) = (num r,(b,[(t,num r)|(t,r)<-edges]))
