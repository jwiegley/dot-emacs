(* 
   Isabelle configuration for Proof General.

   Author:  David Aspinall <da@dcs.ed.ac.uk>
   Contact: Isabelle maintainer <isabelle@dcs.ed.ac.uk>

   $Id$

*)


use "/home/da/isa-patches/thy_read.ML";
open ThyRead;


signature PROOFGENERAL =
sig
   val kill_goal : unit -> unit
   val help : unit -> unit
   val show_context : unit -> unit
   val retract_file : string -> unit
end

structure ProofGeneral =
  struct
    (* Some top-level commands for Proof General.
       These easily could be customized to do different things.
    *)

    fun kill_goal () = Goal "PROP no_goal_supplied";
    fun help () = print version;
    fun show_context () = the_context();

    (*  Function used internally by Proof General to track
        dependencies between theory and ML files. *)

    fun retract_file thy =
     let fun file_msg x = if (x <> "") then
			writeln ("Proof General, you can unlock the file "
			     ^ (quote x))
	               else ()
         fun show_msgs thy =
           let val (thy_file, ml_file) = get_thy_filenames (path_of thy) thy
            in (file_msg thy_file; file_msg ml_file) end

         fun already_loaded thy =
           let val t = get_thyinfo thy
           in if is_none t then false
              else let val {thy_time, ml_time, ...} = the t
           in is_some thy_time andalso is_some ml_time end
         end

         fun children_loaded thy = 
         let val children = children_of thy
	     val present = filter (is_some o get_thyinfo) children;
          in filter already_loaded present end
      in      
       if already_loaded thy then
	 (show_msgs thy; map retract_file (children_loaded thy); ())
       else ()
   end;
  end;       

(* add markup to proof state output *)

val proof_state_special_prefix="\248";
val proof_state_special_suffix="\249";
val goal_start_special="\253";

current_goals_markers:=(proof_state_special_prefix,
			proof_state_special_suffix,
		        goal_start_special);



(* Turn on verbose update output, Proof General likes to parse it. *)
update_verbose:=true;

(* Let Proof General see the theories loaded in the logic image. *)
update();


  

