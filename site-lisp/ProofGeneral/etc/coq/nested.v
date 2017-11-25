(* Testing nested Proofs, and backtrack mechanism in general.

    BUGS:

    - Nested sections...

======= Below here fixed

    - Retract 7a -> 6  needs to do 3 sorts of undo commands!  
      Abort, Undo, Back.
      Algorithm is to use current search-forwards from target span
      mechanism, which has to cover the whole range of undo to count
      all the Backs. However, only the initial Undo's which appear 
      before an Abort need to be counted.  (See coq-find-and-forget).

    - Undo of "Require Omega" in proof uses Undo instead of Back.
      [ coq-count-undos needs fixing to use Back as well as Undo ? ]

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


Section Apple.

(* 2a. *)
Fixpoint f [n:nat] : nat := Cases n of O => O | (S m)=> (f m) end. 
(* 2b.  Retraction to 2a from here uses "Reset".  
   Retraction to 2a from inside proof uses "Abort. Back." *)


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
Definition foo:=O. (* 6.5 between 6 and 7 *)
Require Omega. (* 7 This needs "Back 1" to be retracted. *)
  Lemma t2 : O=O.   (* 7a. -> 6: "Abort. Back 1. Undo 1." *)
    Auto. 
    Print f.        (* a non-undoable "tactic" *)
    Lemma t4 : O=O. 
       Auto.        (* 7b. -> 6: "Abort. [Undo.] Abort. Back 1. Undo 1." *)
		    (* 7b. -> 2: "Abort. Abort. Abort. Back 1."
		       This is a useful test case because PG splits
		       undo calculation into phases: outwith
		       top-level proof and within top-level proof. *)
    Save.
  Save. (* 8 "Back 1" or "Reset t2". *)
  Proof.  (* another non-undoable... *)
Intros. (* 9 "Undo": example of retraction 9->6: Undo 2.  Back 3. *)
  Fixpoint g [n:nat] : nat := Cases n of O => O | (S m)=> (g m) end. (*7*)
  Lemma t3 : O=O. Auto. Save. (* 10 "Back 1" or "Reset t3" *)
EAuto. (* 11 "Undo" *)
Save. (* 12 *)

End Apple.

Section Banana.

Lemma Coq:  O=O. Auto. Save.   (* silly example to show that testing
				  prompt in coq-proof-mode-p to determine 
				  if we're in proof mode is not good enough. 
				  Hopefully nobody calls their theorems "Coq".*)

End Banana.

(* Nested sections?  
   Oh no, this is too horrible to even think about.  *)

Section Cranberry.

  Section Damson.
   
    Lemma CoqIsStrange:  O=O. Auto. Save.

  End Damson.

End Cranberry.
