(* Test of completed proof behaviour: even if qed command is missing,
   PG should close of the proof as a goalsave.

   Issue with Isabelle2002: Goals.disable_pr prevents
   proof-shell-proof-completed being set because "No Subgoals!" is not
   displayed.  This means that processing file in one go here (or C-c
   C-RET at val_) does not work properly.
*)

(* default proof-completed-proof-behaviour for isa is 'closeany. 
   Also should test this file with 'closegoal, 'extend.
      
    (setq proof-completed-proof-behaviour 'closeany)  
     : close on any command after proof completed seen
    (setq proof-completed-proof-behaviour 'closegoal)
     : close when next goal is seen
    (setq proof-completed-proof-behaviour 'extend)
     : continually extend region after proof completed, until next goal.

 *)

Goal "A & B --> B & A";
  by (rtac impI 1);
  by (etac conjE 1);
  by (rtac conjI 1);
  by (assume_tac 1);
  by (assume_tac 1);
  (* qed "and_comms"; *)

val _ = ();
val _ = ();

Goal "A & B --> B & A";
  by (rtac impI 1);
  by (etac conjE 1);
  by (rtac conjI 1);
  by (assume_tac 1);
  by (assume_tac 1);
  qed "and_comms";




