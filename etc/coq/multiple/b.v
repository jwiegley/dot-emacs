(* Silly tests for automatic auto file handling *)

Goal (A,B:Prop)(and A B) -> (and B A).
Intros A B H.
Induction H.
Apply conj.
Assumption.
Assumption.
Save and_comms_b.


