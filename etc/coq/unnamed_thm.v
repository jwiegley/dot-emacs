(*
    Test for Unnamed_thm
 
    $Id$
*)

(* Coq calls this "Unamed_thm", so must forget it like any other *)

(* test: do, undo, then check shell buffer to see "Reset Unnamed_thm" *)

Goal (A,B:Prop)(and A B) -> (and B A).
Intros A B H.
Induction H.
Apply conj.
Assumption.
Assumption.
Save.   

(* Odd side effect: two unnamed theorems in a row are not possible! *)

Goal (A,B:Prop)(and A B) -> (and B A).
Intros A B H.
Induction H.
Apply conj.
Assumption.
Assumption.
Save.   



