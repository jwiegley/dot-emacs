module ScopeNamesPropStruct where
import ScopeNames
import ScopeNamesBaseStruct(extdef,exttvar,pairEnv)
import DefinedNames
import DefinedNamesPropStruct()
import FreeNames
import PropSyntaxStruct
--import MUtils
import EnvM

--extdef ext b = inModEnv . ext $ definedNames b

instance (ScopeNames i e pa1 pa2,ScopeNames i e pp1 pp2)
      => ScopeNames i e (PD i pa1 pp1) (PD (i,e) pa2 pp2) where
  scopeNames ext pd =
      case pd of
	HsPropDecl s n is p -> ex is scAll
	_ -> scAll
    where
      scAll = seqPD $ mapPD pairEnv m m pd
      ex ns = inModEnv (ext [(n,Value)|n<-ns])
      m x = scopeNames ext x

instance (ScopeNames i e e1 e2, ScopeNames i e t1 t2,FreeNames i t1,
          ScopeNames i e pa1 pa2, ScopeNames i e pp1 pp2)
      => ScopeNames i e (PA i e1 t1 pa1 pp1) (PA (i,e) e2 t2 pa2 pp2) where
  scopeNames ext pa =
      case pa of
	   -- The type variables in t scope over the whole expression
	Quant q i t pa' -> exttvar ext t (ex [HsVar i] scAll)
        _ -> scAll
    where
      scAll = seqPA $ mapPA pairEnv sc sc sc sc pa
      ex ns = inModEnv (ext [(n,Value)|n<-ns])
      sc x = scopeNames ext x

instance (ScopeNames i e e1 e2, ScopeNames i e p1 p2, ScopeNames i e t1 t2,
          ScopeNames i e pa1 pa2, ScopeNames i e pp1 pp2,
	  DefinedNames i p1,FreeNames i t1)
      => ScopeNames i e (PP i e1 p1 t1 pa1 pp1) (PP (i,e) e2 p2 t2 pa2 pp2) where
  scopeNames ext pp =
      case pp of
	PredLfp i optt pp' -> ex [HsCon i] scAll
	PredGfp i optt pp' -> ex [HsCon i] scAll
	PredComp pts pa ->
	   -- The type variables in pts scope over the whole expression
	  extdef ext (map fst pts) (exttvar ext (map snd pts) scAll)
        _ -> scAll
    where
      scAll = seqPP $ mapPP pairEnv m m m m m pp
      ex ns = inModEnv (ext [(n,Property)|n<-ns])
      m x = scopeNames ext x
