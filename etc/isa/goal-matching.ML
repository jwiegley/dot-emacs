(* 
   Test case sent by David von Oheimb.
   Bug in matching case-insensitively meant that
   the SELECT_GOAL line was considered a goal.
   Apparently.  Haven't been able to reproduce.
*)

Goal "x";
by (SELECT_GOAL all_tac 1);


