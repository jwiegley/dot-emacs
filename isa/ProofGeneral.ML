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
   val retract_ML_file : string -> unit
   val retract_thy_file : string -> unit
   val repeat_undo : int -> unit
   val clear_response_buffer : unit -> unit
   val list_loaded_files : unit -> unit
   val use_thy_and_update : string -> unit
   val special_theories : string list ref
end;

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

    fun retract_file1 not_thy filename =
     let val (path, tname) = split_filename filename
         fun file_msg x = if (x <> "") then
			writeln ("Proof General, you can unlock the file "
			     ^ (quote x))
	               else ()
         fun show_msgs thy =
           let val (thy_file, ml_file) = get_thy_filenames (path_of thy) thy
            in (if not_thy then ()
		   else file_msg thy_file; 
		file_msg ml_file) end
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
       if already_loaded tname then
	 (show_msgs tname; 
	  map (retract_file1 false) (children_loaded tname); ())
       else ()
   end;

   (* retract a script file and all it's theory/script children,
       but not it's parent theory. *)

   val retract_ML_file = retract_file1 true;

   (* retract a theory file and all it's theory/script children *)

   val retract_thy_file = retract_file1 false;
   

   fun repeat_undo 0 = ()
     | repeat_undo n = (undo(); repeat_undo (n-1));

   fun clear_response_buffer () =
      writeln("Proof General, please clear the response buffer.");

   val special_theories = ref ["ProtoPure", "Pure", "CPure"];
   
   fun list_loaded_files () =
   let
     val thys_list = Symtab.dest (!loaded_thys)
     fun loading_msg (tname,tinfo) =
        if (tname mem (!special_theories)) then () else
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
    (writeln "Updating loaded files list...";
     seq loading_msg thys_list)
   end;

 (* 
   Possible alternative: parse "children are out of date"
   message, and unlock those ones (plus descendants).
   This seems feasible, but use_thy ought to do update
   anyway, I think. 
  *)

  fun use_thy_and_update thy = 
  (use_thy_no_topml thy;
   update();
   list_loaded_files();
   clear_response_buffer());

 end; (* struct ProofGeneral *)

 fun remove_mlfile_fromdb thy =
  let val tinfo =  case Symtab.lookup (!loaded_thys, thy) of
	Some ({path, children, parents = parents, thy_time, theory,...}) =>
	{ path = path, children = children, parents = parents, theory=theory,
          thy_time = thy_time, ml_time = None }
             | None => error 
	 ("remove_mlfile_from_db: theory " ^ thy ^ " not found");
    in  loaded_thys := Symtab.update ((thy, tinfo), !loaded_thys) end;


(*
fun use_thy_and_update thy =
  (use_thy_no_topml thy;   (* don't read ML but will be in db [useful bug]*)
   update () 		   (* fixup dependencies left broken by use_thy
	(question: can it re-read the top ML, though??  hope not) *)
    handle exn => 
       (remove_mlfile_fromdb thy handle _ => raise exn; raise exn);  
   remove_mlfile_fromdb thy);
*)


(* Temporary hack. *)
(* 
 NB: this has bad behaviour because update will force loading of
   the theory file if used again later.  Need a test case for 
   this, and to fix it.
*)


(* configure output channels to decorate output *)

local
  fun quickout s = TextIO.output (TextIO.stdOut, s);
  fun out s =
    (TextIO.output (TextIO.stdOut, s); TextIO.flushOut TextIO.stdOut);
  fun outnl s =     
    (TextIO.output (TextIO.stdOut, s^"\n"); TextIO.flushOut TextIO.stdOut);

  fun prefix_lines_specials spec prfx txt sufx =
    txt |> split_lines |> map (fn s => spec ^ prfx ^ s ^ sufx ^ "\n")
	|> implode;

  (* Problem with writeln: it's hardwired to do out (s^"\n") but
     we really want annotations to appear before carriage returns.
     This hack deals with the last CR in a string.
  *)	
  fun out_with_hacked_last_cr startspec str endspec =
   (quickout startspec;
    case (rev (split_lines str)) of
         [] => out endspec
       | ""::rest => (seq outnl (rev rest);
		      out endspec)
       | _ => (quickout str; out endspec))
in
    (* \240 is octal 360, first special character used. *)
    val _ =
      (prs_fn := 
	   (fn s => out_with_hacked_last_cr "\240" s "\241");
       warning_fn :=
	   (fn s => out (prefix_lines_specials "\242" "### " s "\243"));
       error_fn :=
	   (fn s => out (prefix_lines_specials "\244" "*** " s "\245")))
	   
end;

(* add markup to proof state output *)

val proof_state_special_prefix="\246";  (* ?\366 *)
val proof_state_special_suffix="\247";  (* ?\367 *)
val goal_start_special="\248";	        (* ?\370 *)

current_goals_markers:=(proof_state_special_prefix,
			proof_state_special_suffix,
		        goal_start_special);

local
  fun out s =
    (TextIO.output (TextIO.stdOut, s); TextIO.flushOut TextIO.stdOut);
in
  fun print_current_goals_with_plain_output i j t =
    Library.setmp prs_fn out (print_current_goals_default i j) t;

  (* Annoyingly, Proof General waits for the first prompt before doing
     anything.  Hack sending a prompt to get things going *)

  val _ = out "> \n";
end;

print_current_goals_fn := print_current_goals_with_plain_output;


(* add specials to ml prompts *)

(*
   ml_prompts ">\250" "-\251"; (* ?\372, ?\373 *)
   
   NB: Obscure bug with proof-shell-annotated-prompt-regexp set
   properly to include annotations: PG doesn't recognize first proof
   state output.
*)   


(* Turn on verbose update output, Proof General likes to parse it.
      update_verbose:=true;
   Unfortunately broken.  We use list_loaded_files instead. *)

(* Get Proof General to cache the loaded files.  *)

ProofGeneral.list_loaded_files();
ProofGeneral.clear_response_buffer();
writeln "Isabelle Proof General: Isabelle process ready!";





