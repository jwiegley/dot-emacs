(*
    Example proof script for HOL Proof General.

    $Id$
*)    

g `A /\ B ==> B /\ A`;
e DISCH_TAC;
e CONJ_TAC;
e (IMP_RES_TAC AND_INTRO_THM);
e (IMP_RES_TAC AND_INTRO_THM);
val and_comms = top_thm(); drop();

(* this is not quite like the other proofs, 
   can anyone tell me a more similar proof in HOL? *)