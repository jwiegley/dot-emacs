(* Coq theorems, etc can be named at the top .... *)

Theorem and_comms: (A,B:Prop)(A /\ B) -> (B /\ A).
  Intros A B H.
  Induction H.
  Apply conj.
  Assumption.
  Assumption.
Qed.

(* at the bottom... *)

Goal (A,B:Prop)(A /\ B) -> (B /\ A).
  Intros A B H.
  Induction H.
  Apply conj.
  Assumption.
  Assumption.
Save and_comms2.

(* or not at all! *)
(* Coq calls this "Unamed_thm", so must forget it like any other *)
(* test: do, undo, then check shell buffer to see "Reset Unnamed_thm" *)

Goal (A,B:Prop)(A /\ B) -> (B /\ A).
  Intros A B H.
  Induction H.
  Apply conj.
  Assumption.
  Assumption.
Save.

(* Odd side effect: two unnamed theorems in a row are not possible! *)

(* TESTING: notice output window behaviour here with different settings:
   exact output displayed also depends on how many steps are issued
   at once.
*)

Goal (A,B:Prop)(and A B) -> (and B A).
Intros A B H.
Induction H.
Apply conj.
Assumption.
Assumption.
Save.   



