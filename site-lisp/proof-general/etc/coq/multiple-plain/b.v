(* Simple tests for multiple file handling *)

Goal forall (A B:Prop),(A /\ B) -> (B /\ A).
  intros A B H.
  elim H.
  intros.
  split.
  assumption.
  assumption.
Save and_comms_b.
