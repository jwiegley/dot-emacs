Module GoalGoal;

Goal first : {A:Prop}A->A;
intros; Immed;
(* no Save *)

Goal second : {A:Prop}A->A;
intros; Immed;
Save second;
(* asserting until here caused Proof General to swap first and second.
This is a bug for LEGO. Thanks to Martin Hofmann for pointing this
out. An obvious bug fix would be to make the function
proof-lift-global Coq specific. *)