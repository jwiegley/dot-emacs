(*
    Example nested proof script for testing support of nested proofs.
*)

Goal (A,B:Prop)(A /\ B) -> (B /\ A).
  Intros A B H.
  Induction H.
  Apply conj.
  Lemma foo: (A,B:Prop)(A /\ B) -> (B /\ A).
    Intros A B H.
    Induction H.
    Apply conj.
    Assumption.
    Assumption.
  Save.
  Assumption.
  Assumption.
Save and_comms.

