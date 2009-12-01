(*
    Example proof script for Coq Proof General.

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
