(*
    Example proof script for Coq Proof General (Coq V8 syntax).

    $Id$
*)

Module Example.

Goal forall (A B:Prop),(A /\ B) -> (B /\ A). 
  intros A B.
  intros H.
  elim H.
  split.
  assumption.
  assumption.
Save and_comms.

End Example.
