module NondetMachine where
import FSM
import FSMOpt
import GraphOps
import MUtils(collectByFst,collectBySnd,usort)
import qualified IntMap as M
import qualified IntSet as S

-- Simulation of nondeterministic finite state machines

data NondetState i o = N (Map [(Edge (Trans i o),State)]) (Map S.IntSet) [State]

initM (NFA graph) start = goto (N graph epsg []) [start]
  where
    epsg = transitiveClosure (epsilonconnectivity graph)

goto (N g eg _) ss = N g eg (usort (concatMap (neighbourlist eg) ss))

accept state@(N g eg ss) t =
   case [s'|s<-ss,(T (I t'),s')<-next s,t'==t] of
     [] -> case unzip [(o,s')|s<-ss,(T (O o),s')<-next s] of
             (os,ss') -> Left (os,goto state ss')
     ss' -> Right (goto state ss')
  where
    next = M.lookupWithDefault g []

runM state = run [] state
  where
    run as state@(N _ _ []) is = [Right ([],reverse as),Left []]
    run as state@(N _ _ ss) [] = [Right ([],reverse as)]
    run as state@(N _ _ ss) (i:is) =
      Left ss:
      case accept state i of
	Right state -> run (i:as) state is
	Left (os,state) -> Right (os,reverse as):run [] state (i:is)

canAccept (N g eg ss) =
   collectBySnd . collectByFst $
   [(t,s') | s<-ss,(T (I t),s')<-M.lookupWithDefault g [] s]

canOutput (N g eg ss) =
   collectBySnd . collectByFst $
   [(t,s') | s<-ss,(T (O t),s')<-M.lookupWithDefault g [] s]
