(*
    Example proof script for Coq Proof General (Coq V8 syntax).

    $Id$
*)

Goal forall (A B:Prop),(A /\ B) -> (B /\ A).
  intros A B H.
  elim H.
  intros.
  split.
  assumption.
  assumption.
Save and_comms.
