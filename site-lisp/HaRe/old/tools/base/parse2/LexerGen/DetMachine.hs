module DetMachine where
import NondetMachine
import FSM
import DFA(DFA(..))
import qualified OrdMap as OM

-- Representation of Deterministic Finite State Machines:

type DState = [State]

-- Translation of nondeterministic to deterministic state machines:

deterministicMachine ((start,final),nfa) =
    ((states inited,finalstates),DFA detm)
  where
    inited = initM nfa start
    detm = determine inited (OM.empty)
    determine state@(N g eg ss) detm =
      case OM.lookup ss detm of
        Just _ -> detm
	Nothing ->
	    foldr determine detm' next
	  where
	    detm' = OM.add (ss,(ithis,othis)) detm
	    next = map snd onext++map snd inext
	    inext = getnext canAccept
	    onext = getnext canOutput
	    ithis = this inext
	    othis = this onext
	    this next = [(t,states ss)|(ts,ss)<-next,t<-ts]
	    getnext f = [(ts,goto state ss)|(ts,ss)<-f state]

    finalstates = [ss | ss<-OM.indices detm,final `elem` ss]

states (N _ _ ss) = ss
