(* 
   Isabelle configuration for Proof General.

   Author:  David Aspinall <da@dcs.ed.ac.uk>
   Contact: Isabelle maintainer <isabelle@dcs.ed.ac.uk>

   $Id$

*)


(*
 use "/home/da/isa-patches/thy_read.ML";
 open ThyRead;
*) 


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

fun remove_mlfile_fromdb thy =
  let val tinfo =  case Symtab.lookup (!loaded_thys, thy) of
	Some ({path, children, parents = parents, thy_time, theory,...}) =>
	{ path = path, children = children, parents = parents, theory=theory,
          thy_time = thy_time, ml_time = None }
             | None => error 
	 ("remove_mlfile_from_db: theory " ^ thy ^ " not found");
    in  loaded_thys := Symtab.update ((thy, tinfo), !loaded_thys) end;


fun use_thy_and_update thy =
  (use_thy_no_topml thy;   (* don't read ML but will be in db [useful bug]*)
   update () 		   (* fixup dependencies left broken by use_thy
	(question: can it re-read the top ML, though??  hope not) *)
    handle exn => 
       (remove_mlfile_fromdb thy handle _ => raise exn; raise exn);  
   remove_mlfile_fromdb thy);

fun list_loaded_files () =
 let
   val thys_list = Symtab.dest (!loaded_thys)
   fun loading_msg (tname,tinfo) = 
	let val path = path_of tname
	    val (thy_file,ml_file) = get_thy_filenames path tname
	    fun file_msg x = if (x <> "") then
			(* Simulate output of theory loader *)
			writeln ("Reading " ^ (quote x))
	               else ()
	  in
	     (file_msg thy_file; file_msg ml_file)
          end
  in
    seq loading_msg thys_list
  end;

   

(* configure output channels to decorate output *)

(*
 Frustratingly, Isabelle uses prs_fn also when displaying
 the goal state, so it's no use setting that hoping to catch
 all "normal" output separately.  We really need a fourth
 output channel.
 *)
	       
local
  fun out s =
    (TextIO.output (TextIO.stdOut, s); TextIO.flushOut TextIO.stdOut);

  fun prefix_suffix_lines prfx txt sufx  =
    txt |> split_lines |> map (fn s => prfx ^ s ^ sufx ^ "\n") |> implode;
in
    val _ =
      (* No difference to original functions at the moment. *)
      (prs_fn := (fn s => out s) ;
       warning_fn :=  (fn s => out (prefix_suffix_lines "### " s "")) ;
       error_fn := (fn s => out (prefix_suffix_lines "*** " s "")))
end;


(* add markup to proof state output *)

val proof_state_special_prefix="\248";
val proof_state_special_suffix="\249";
val goal_start_special="\253";

current_goals_markers:=(proof_state_special_prefix,
			proof_state_special_suffix,
		        goal_start_special);



(* Turn on verbose update output, Proof General likes to parse it.
      update_verbose:=true;
   Unfortunately broken.  We use list_loaded_files instead. *)

(* Get Proof General to cache the loaded files. *)

list_loaded_files();



  

