(*
    Example proof script for Coq Proof General (Coq V8 syntax).

    $Id$
*)

Goal forall (A B:Prop),(A /\ B) -> (B /\ A).
  intros A B.
  intros H.
  elim H.
  split.
  assumption.
  assumption.
Save and_comms.
