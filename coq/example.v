(*
    Example proof script for Coq Proof General.
 
    $Id$
*)

Goal (A,B:Prop)(and A B) -> (and B A).
Intros A B H.
Induction H.
Apply conj.
Assumption.
Assumption.
Save and_comms.
