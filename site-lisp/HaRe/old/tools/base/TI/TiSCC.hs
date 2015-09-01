module TiSCC where
--import TiClasses
import MUtils
import NewSCC
--import Grapheq
import Data.Maybe(fromJust,mapMaybe)
import TiDefinedNames(definedNamesSplit)
import TiFreeNames

default(Int)

sccD' names ds = map (map (def.fst)) (scc graph)
  where
    --scc = scceq (==)
    def n = fromJust (lookup n ndefs)
    graph = [(n,mapMaybe refs xs)|(n,(_,xs))<-nvars]
    refs x = lookup x defnrs
    ndefs = zip [0..] ds
    nvars = mapSnd names ndefs
    
    defnrs = [(x,n)|(n,(xs,_))<-nvars,x<-xs]
  
sccD ds = sccD' names ds
  where
    names d =
      case definedNamesSplit d of
	([],[]) -> ([],[])
	(types,[]) -> (types,freeTypeNames d)
        ([],values) -> (values,freeValueNames d)
	_ -> error "TiSCC.hs: mixed type/value definition"
