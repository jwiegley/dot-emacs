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
   val repeat_undo : int -> unit
   val clear_response_buffer : unit -> unit

   (* Processing used files *)
   (* retract_thy_file f:
        Send messages to Proof General to unlock children of theory file f
      retract_ML_file f:
        Send messages to Proof General to unlock children of script file f
      list_loaded_files ():
        Messages to Proof General listing all loaded files
      update ():
        Run update with messages to re-synchronize loaded files.
   *)
   val retract_ML_file : string -> unit
   val retract_thy_file : string -> unit
   val list_loaded_files : unit -> unit
   val update : unit -> unit
   val restart : unit -> unit
   
   (*  visible only for testing *)
   val loaded_parents_of : string -> string list
   val loaded_files : unit -> string list
   val apply_and_update_files : ('a -> 'b) -> 'a -> unit
   val use_thy_and_update : string -> unit  (* not used *)
   val use_thy : string -> unit
   val initial_loaded_thys : thy_info Symtab.table ref
   val special_theories : string list ref
   val retracted_files : string list ref
end;

structure ProofGeneral : PROOFGENERAL =
  struct
    (* Some top-level commands for Proof General. *)

    fun kill_goal () = (Goal "PROP no_goal_supplied"; ())
    fun help () = print version;
    fun show_context () = (the_context(); ())

    (* Function used by undo operation *)
    
    fun repeat_undo 0 = ()
      | repeat_undo n = (undo(); repeat_undo (n-1));

    (* State *)

    (* Theories which have no .thy or .ML files *)	
    val special_theories = ref ["ProtoPure", "Pure", "CPure"];

    (* Cache of retracted files: see notes below. *)
    val retracted_files = ref [] : string list ref;

    (* Copy of theory database *)
    val initial_loaded_thys = ref (!loaded_thys);

    (* Messages to Proof General *)

    fun retract_msg x = writeln ("Proof General, you can unlock the file "
			         ^ (quote x))
    fun process_msg x = writeln ("Proof General, this file is loaded: "
			         ^ (quote x))
    fun msg_unless_empty f x = if (x<>"") then f x else ();

    fun clear_response_buffer () =
       writeln("Proof General, please clear the response buffer.");
       

    (*
      FIXME future function, to help synchronize in event of an error.
      fun clear_msg x = writeln
        ("Proof General, please clear your record of loaded files.")
    *)

    (*  Functions used internally by Proof General to track
        dependencies between theory and ML files. *)

   (* LISTING LOADED FILES
        Next few functions tell Proof General what files are
	loaded into Isabelle.
    *)
      	
   (* subroutine: return loaded files for theory named tname *)
   fun loaded_files_for thys =
     let fun loaded_for tname =
     if (tname mem (!special_theories)) then [] else
	let val path = path_of tname
	    val (thy_file,ml_file) = get_thy_filenames path tname
	    fun file_name x = if (x <> "") then [x] else []
	in (file_name thy_file) @ (file_name ml_file) end
     in
        foldl (op @) ([], map loaded_for thys)
     end 

   (* Return a list of the loaded files in the theory database *)
   fun loaded_files () = loaded_files_for
				(map fst (Symtab.dest (!loaded_thys)))

   (* List all the loaded files in the theory database.
      Clears the list of retracted files.
   *)
   fun list_loaded_files () =
   let
     val _ = retracted_files := []
   in     
    (writeln "Setting loaded files list...";
     seq (msg_unless_empty process_msg) (loaded_files());
     writeln "Done.")
   end

   (* RESTARTING *)

   fun restart () =
     let val _ = (loaded_thys := !initial_loaded_thys)
         val _ = (retracted_files := [])
	 val _ = (kill_goal ())
      in
         (list_loaded_files();
          clear_response_buffer();
          writeln "Isabelle Proof General: Isabelle process ready!")
      end;


    (*
      RETRACTION:
         We keep some state here to record what files Proof General
	 thinks have been retracted.
	 Really this shouldn't be necessary but it gets round
	 some of the mess of the theory loader.
	 
     *)

    (* subroutine: retract a file and give message, if it hasn't
       been already reported to Proof General. *)
       
    fun retract_file_and_give_message filename =
      if filename="" orelse (filename mem !retracted_files) then ()
      else (retract_msg filename;
	    retracted_files := filename :: !retracted_files;
	    ())

    fun retract_file1 not_thy filename =
     let val (path, tname) = split_filename filename
         fun show_msgs thy =
           let val (thy_file, ml_file) = get_thy_filenames (path_of thy) thy
            in (if not_thy then ()
		   else retract_file_and_give_message thy_file; 
		retract_file_and_give_message ml_file) end
         (* Only considered loaded if both theory and ML times set *)
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


   (* USING files.
        When a file is used by Isabelle, Proof General wants to know
	all it's ancestor files which are loaded automatically.
	The theory loader only loads files if they've changed,
	so we use the cache of retracted files to pretend more
	have been loaded.
    *)

   (* Find the loaded parents of a file (including the file itself) *)
   fun loaded_parents_of filename =
   let
      val (path, tname) = split_filename filename
      fun already_loaded thy =
      let val t = get_thyinfo thy
       in if is_none t then false
          else let val {thy_time, ml_time, ...} = the t
        in is_some thy_time andalso is_some ml_time end
      end
      fun gather_parents parents thys =
	 let val next_parents = foldl (op union) ([],map parents_of_name thys)
	     val interesting_parents = filter already_loaded next_parents
	     val new_parents = interesting_parents \\ parents
	  in case new_parents of
	       [] => parents
	     | _ => gather_parents (parents union new_parents) new_parents
	  end
      in      
       if (already_loaded tname) 
       then loaded_files_for (gather_parents [tname] [tname])
       else []
   end;

   (*  List the parents of a loaded file *)
   (* not used *)   
   fun list_parents_with f filename =
      seq (msg_unless_empty f) (loaded_parents_of filename)
      
   (* Function to do a "use" operation.
       Only consider the parents of a theory, because its
       children should be unlocked at this point,
       and not get locked by the use operation.

       We consider the current parents to be the ones in the
       database less those retracted up to now.

       Using a theory can lock new files which
       are parents of the theory being used.
       It cannot unlock files.
    *)
           
     fun use_thy1 use_fn thy =
     let
      val parents_before = (loaded_parents_of thy) \\ (!retracted_files)
      val _ = (use_fn thy) handle ex =>
			(list_loaded_files(); raise ex)
      val parents_after = loaded_parents_of thy
      val parents_added = parents_after \\ parents_before
      val _ = retracted_files := ((!retracted_files) \\ parents_added)
     in     
       (seq process_msg parents_added)
     end


    (* Use a theory file but not it's top-level ML file *)
    val use_thy = use_thy1 use_thy_no_topml;

    

   (* Function to do an "update" operation.
       This is like the use operation above except that we
       consider all of the loaded files, since update can make
       change anywhere.   It may also load top-level ML
       files which is a bit of a nuisance.
    *)

   fun apply_and_update_files update_fn x =
   let val files_before = loaded_files() \\ !retracted_files
       val _ = update_fn x
       val files_after = loaded_files()
       val files_added = files_after \\ files_before 
       val files_removed = files_before \\ files_after
    in
      (seq retract_msg files_removed;
       seq process_msg files_added)
    end

  (* Update and re-list loaded files and deletions.
      *)
  val update = apply_and_update_files update;


  (* not used *)
  fun use_thy_and_update thy = 
  (use_thy_no_topml thy;
   update();
   list_loaded_files();
   clear_response_buffer())

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

(* Proof General has problems sending commands outside of the
   action list.  Also, it waits for the first prompt before doing
   anything.  The next function hacks sending a prompt to get
   things going and to help fix things later. *)

  fun hack_send_prompt _ = out ">\250 \n";
end;

print_current_goals_fn := print_current_goals_with_plain_output;


(* add specials to ml prompts *)

ml_prompts ">\250" "-\251"; (* ?\372, ?\373 *)


(*
   NB: Obscure bug with proof-shell-annotated-prompt-regexp set
   properly to include annotations: PG doesn't recognize first proof
   state output.
*)   


(* Turn on verbose update output, Proof General likes to parse it.
      update_verbose:=true;
   Unfortunately broken.  We use list_loaded_files instead. *)


(* Wake up, Proof General! *)
hack_send_prompt();

(* Get Proof General to cache the loaded files.  *)
ProofGeneral.restart();
