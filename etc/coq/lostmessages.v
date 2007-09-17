(* These are some examples which generate goals and errors at the same
   moment.  May be broken in development version of Coq.
   
   See  http://proofgeneral.inf.ed.ac.uk/trac/ticket/141 
*)

Require Import Setoid. 
Goal False. 
setoid_replace False with True.

Goal True /\ True -> True. 
intro H. 
destruct H as [H1 H2 H3].
