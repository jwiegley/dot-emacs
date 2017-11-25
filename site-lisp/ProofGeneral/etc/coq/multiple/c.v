(* Simple tests for multiple file handling *)

Require d.  (* d requires a *)
Require a.
Require b.

Goal forall (A B:Prop),(A /\ B) -> (B /\ A).
  intros A B H.
  elim H.
  intros.
  split.
  assumption.
  assumption.
Save and_comms_c.
