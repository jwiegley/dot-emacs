(* 
   Isabelle/Isar configuration for Proof General.

   Author:  David Aspinall <da@dcs.ed.ac.uk>
   Contact: Isabelle maintainer <isabelle@dcs.ed.ac.uk>

   ProofGeneral.ML,v 2.16 1998/11/03 16:29:30 da Exp

MMW: I have temporarily removed the theory loader patches, since it
kept crashing on me.
*)


(** configure output channels to decorate output **)

(*messages*)
writeln_fn :=
  (std_output o suffix "\n" o enclose (oct_char "360") (oct_char "361"));
warning_fn :=
  (std_output o suffix "\n" o enclose (oct_char "362") (oct_char "363") o prefix_lines "### ");
error_fn :=
  (std_output o suffix "\n" o enclose (oct_char "364") (oct_char "365") o prefix_lines "*** ");

(*prompts*)
Source.decorate_prompt_fn := (fn s => s ^ oct_char "372");

(*theory / proof state*)
current_goals_markers :=
  let
    val begin_state = oct_char "366";
    val end_state= oct_char "367";
    val begin_goal = oct_char "370";
  in (begin_state, end_state, begin_goal) end;

Toplevel.print_state_fn :=
  (Library.setmp writeln_fn (std_output o suffix "\n") Toplevel.print_state_default);


print_mode := ["ProofGeneral"];

Isar.main();
