(*
    Example proof script for Coq Proof General.
 
    $Id$
*)


Goal (A,B:Prop)(A /\ B) -> (B /\ A).
Intros A B H.
Induction H.
Apply conj.
Assumption.
Assumption.
Save and_comms.

