module Minimalize where
import DFA
import MUtils(usort,mapSnd,collectBySnd)
import qualified OrdMap as OM
import Maybe(fromMaybe)

minimalize (s,DFA states) = iter [] (s,OM.toList states)
  where
    iter eqs dfa = case equalStates dfa of
	             ([],(s,states)) -> (eqs,(s,DFA (OM.fromList states)))
		     (eqs',dfa) -> iter (eqs':eqs) dfa

equalStates ((st,fin),states) =
    (eqclasses,((sren st,usort $ map sren fin),states'))
  where
     eqstates = collectBySnd states
     eqclasses = filter ((>1).length) . map fst $ eqstates
     smap = [(s',s)|s:ss<-eqclasses,s'<-ss]
     sren s = fromMaybe s (lookup s smap)

     states' = map renState eqstates

     renState (s:_,(is,os)) = (s,(nubMapSnd sren is,nubMapSnd sren os))

     nubMapSnd f = usort . mapSnd f
