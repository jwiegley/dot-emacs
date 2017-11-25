(* Coq theorems, etc can be named at the top .... *)

Theorem and_comms: forall (A B:Prop),(A /\ B) -> (B /\ A). 
  intros A B H.
  induction H.
  apply conj.
  assumption.
  assumption.
Qed.

(* at the bottom... *)

Goal forall (A B:Prop),(A /\ B) -> (B /\ A). 
  intros A B H.
  induction H.
  apply conj.
  assumption.
  assumption.
Save and_comms2.

(* or not at all! *)
(* Coq calls this "Unamed_thm", so must forget it like any other *)
(* test: do, undo, then check shell buffer to see "Reset Unnamed_thm" *)

Goal forall (A B:Prop),(A /\ B) -> (B /\ A). 
  intros A B H.
  induction H.
  apply conj.
  assumption.
  assumption.
Save.

(* Odd side effect: two unnamed theorems in a row are not possible! 
   Latest: with Coq 8.2, we get Unamed_thm0, Unamed_thm1, ... *)
Goal forall (A B:Prop),(A /\ B) -> (B /\ A). 
  intros A B H.
  induction H.
  apply conj.
  assumption.
  assumption.
Save.

(* TESTING: notice output window behaviour here with different settings:
   exact output displayed also depends on how many steps are issued
   at once.
*)

Goal forall (A B:Prop),(A /\ B) -> (B /\ A). 
tauto.
Save.   
