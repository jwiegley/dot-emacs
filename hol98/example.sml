(*
    Example proof script for HOL Proof General.

    $Id$
*)    

g `A /\ B ==> B /\ A`;
e DISCH_TAC;
e CONJ_TAC;
e (IMP_RES_TAC AND_INTRO_THM);
e (IMP_RES_TAC AND_INTRO_THM);
val and_comms = pg_top_thm_and_drop();


(* this is not quite like proofs in the other systems, 
   can anyone tell me a more similar proof in HOL? 
   I want to split the IMP_RES_TAC into two steps.  *)