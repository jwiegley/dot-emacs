(* Nested Proofs, and backtrack mechanism in general.
   Bugs:

    - Undo of "Require Omega" in proof uses Undo instead of Back.
      [ coq-count-undos needs fixing to use Back as well as Undo ? ]

======= Below here fixed?

    - once point 12 is reached, sould have one
      block from 3 to 12. With the goalsave test :
      OK but the reset command is wrong.

    - From point 5, retract to point 1: "Abort. Back 5." Argl
      Wrong, tactics and line 3 are counted for Back!!
      This comes from my modification of coq-find-and-forget
      function.

    - point 7 is not well backtracked, but this can be solved easily
      in coq.el.
 *)

Require Logic. (* 1 This needs "Back 1" to be retracted *)
Require List. (* 2 This needs "Back 1" to be retracted *)


Lemma t1: (n: nat ) {n=O} + {(EX y | n = (S y))}.  
(* 3 This needs "Restart" to be retracted if inside the proof, and
"Reset t1. Back 4."  if outside (after point 12). 3 because of the
Require and the two lemmas inside the proof. If only "Reset t1", like
with the current version of PG, then t2 and t3 are still in the
environment. Try this with the current version and with my patch *)

(* da: Back command seems much better behaved than "Reset", which
   always clears proof state, I think.  Should PG always use Back? *)

Intros. (* 4 This needs "Undo" to be retracted *)
Case n. (* 5 "Undo" *)
EAuto. (* 6 "Undo" *)

Require Omega. (* 7 This needs "Back 1" to be retracted. *)
  Lemma t2 : O=O. Auto. 
    Lemma t4 : O=O. Auto. Save.
  Save. (* 8 "Back 1" or "Reset t2". *)
Intros. (* 9 "Undo" *)
  Lemma t3 : O=O. Auto. Save. (* 10 "Back 1" or "Reset t3" *)
EAuto. (* 11 "Undo" *)
Save. (* 12 *)
