(*
    Example proof script for Coq Proof General.

    $Id$
*)

Goal (A,B:Prop)(A /\ B) -> (B /\ A).
  Intros A B H.
  Elim H.
  Intros.
  Split.
  Assumption.
  Assumption.
Save and_comms.
