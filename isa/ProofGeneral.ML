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
 end;

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




(* Temporary hack. *)
(* 
 NB: this has bad behaviour because update will force loading of
   the theory file if used again later.  Need a test case for 
   this, and to fix it.
*)

(* 
 Possible alternative: parse "children are out of date"
 message, and unlock those ones (plus descendants).
 This seems feasible, but use_thy ought to do update
 anyway, I think. 
*)

fun use_thy_and_update thy = 
  (use_thy_no_topml thy; update(); list_loaded_files());

   

(* configure output channels to decorate output *)

local
  fun out s =
    (TextIO.output (TextIO.stdOut, s); TextIO.flushOut TextIO.stdOut);

  fun prefix_lines prfx txt =
    txt |> split_lines |> map (fn s => prfx ^ s ^ "\n") |> implode;
in
    (* \240 is octal 360, first special character used. *)
    val _ =
      (prs_fn := 
	   (fn s => out ("\240" ^ s ^ "\241"));
       warning_fn :=
	   (fn s => out ("\242" ^ (prefix_lines "### " s) ^ "\243"));
       error_fn :=
	   (fn s => out ("\244" ^ (prefix_lines "*** " s) ^ "\245")))
end;

(* add specials to ml prompts *)

(* disabled because of bugs *)

(* ml_prompts ">\250" "-\251"; *) (* ?\372, ?\373 *)



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
end;

print_current_goals_fn := print_current_goals_with_plain_output;


(* Turn on verbose update output, Proof General likes to parse it.
      update_verbose:=true;
   Unfortunately broken.  We use list_loaded_files instead. *)

(* Get Proof General to cache the loaded files. *)

(* 
list_loaded_files(); 
writeln ("Reading "  ^ (quote "wiggle"));
warning "Could not find blah";

*)

list_loaded_files();

(*
prs "Reading \"/usr/lib/Isabelle98-1/src/HOL/Arith.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Arith.ML\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Integ/Bin.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Integ/Bin.ML\"\n###Could not find file \"CPure.thy\" or \"CPure.ML\" for theory \"CPure\"\n###in the following directories: \".\"\n###File \"CPure.thy\"\n###containing theory \"CPure\" no longer exists.\n###Could not find file \"CPure.thy\" or \"CPure.ML\" for theory \"CPure\"\n###in the following directories: \".\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Datatype.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Divides.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Divides.ML\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Integ/Equiv.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Integ/Equiv.ML\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Finite.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Finite.ML\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Fun.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Fun.ML\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Gfp.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Gfp.ML\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/HOL.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/HOL.ML\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Inductive.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Integ/Int.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Integ/Int.ML\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Integ/IntDef.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Integ/IntDef.ML\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Lfp.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Lfp.ML\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/List.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/List.ML\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Main.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Map.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Map.ML\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Nat.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Nat.ML\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/NatDef.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/NatDef.ML\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Option.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Option.ML\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Ord.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Ord.ML\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Power.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Power.ML\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Prod.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Prod.ML\"\n###Could not find file \"ProtoPure.thy\" or \"ProtoPure.ML\" for theory \"ProtoPure\"\n###in the following directories: \".\"\n###File \"ProtoPure.thy\"\n###containing theory \"ProtoPure\" no longer exists.\n###Could not find file \"ProtoPure.thy\" or \"ProtoPure.ML\" for theory \"ProtoPure\"\n###in the following directories: \".\"\n###Could not find file \"Pure.thy\" or \"Pure.ML\" for theory \"Pure\"\n###in the following directories: \".\"\n###File \"Pure.thy\"\n###containing theory \"Pure\" no longer exists.\n###Could not find file \"Pure.thy\" or \"Pure.ML\" for theory \"Pure\"\n###in the following directories: \".\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Recdef.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Record.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/RelPow.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/RelPow.ML\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Relation.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Relation.ML\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Set.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Set.ML\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Sexp.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Sexp.ML\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/String.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Sum.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Sum.ML\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Trancl.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Trancl.ML\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Univ.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Univ.ML\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Vimage.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/Vimage.ML\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/WF.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/WF.ML\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/WF_Rel.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/WF_Rel.ML\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/equalities.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/equalities.ML\"\nReading \"/home/da/example.thy\"\nReading \"/home/da/example.ML\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/mono.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/mono.ML\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/subset.thy\"\nReading \"/usr/lib/Isabelle98-1/src/HOL/subset.ML\"\n";

  *)



(* Modified theory reader stuff

(*Check if a theory file has changed since its last use.
  Return a pair of boolean values for .thy and for .ML *)
fun thy_unchanged thy thy_file ml_file =
  case get_thyinfo thy of
      Some {thy_time, ml_time, ...} =>
       let val tn = is_none thy_time;
           val mn = is_none ml_time
       in if not tn andalso not mn then
            ((file_info thy_file = the thy_time),
             (file_info ml_file = the ml_time))
          else if not tn andalso mn then
            (file_info thy_file = the thy_time, false)
          else
            (false, false)
       end
    | None => (false, false)

(*Remove a theory from loaded_thys *)
fun remove_thy tname =
  loaded_thys := Symtab.make (filter_out (fn (id, _) => id = tname)

(*Change thy_time and ml_time for an existent item *)
fun set_info tname thy_time ml_time =
  let val tinfo = case Symtab.lookup (!loaded_thys, tname) of
         Some ({path, children, parents, theory, thy_time = _, ml_time = _}) =>
            {path = path, children = children, parents = parents,
                     thy_time = thy_time, ml_time = ml_time, theory = theory}
        | None => error ("set_info: theory " ^ tname ^ " not found");
  in loaded_thys := Symtab.update ((tname, tinfo), !loaded_thys) end;

                 (Symtab.dest (!loaded_thys)));

(*Mark theory as changed since last read if it has been completly read *)
fun mark_outdated tname =
  let val t = get_thyinfo tname;
  in if is_none t then ()
     else
       let val {thy_time, ml_time, ...} = the t
       in set_info tname (if is_none thy_time then None else Some "")
                         (if is_none ml_time then None else Some "")
       end
  end;

(*Directory given as parameter to use_thy. This is temporarily added to
  loadpath while the theory's ancestors are loaded.*)
val tmp_loadpath = ref [] : string list ref;


fun update () =
  let (*List theories in the order they have to be loaded in.*)
      fun load_order [] result = result
        | load_order thys result =
            let fun next_level [] = []
                  | next_level (t :: ts) =
                      let val children = children_of t
                      in children union (next_level ts) end;

                val descendants = next_level thys;
            in load_order descendants ((result \\ descendants) @ descendants)
            end;

      fun reload_changed (t :: ts) =
            let val abspath = case get_thyinfo t of
                                  Some ({path, ...}) => path
                                | None => "";

                val (thy_file, ml_file) = get_thy_filenames abspath t;
		val _ = if thy_file = "" andalso ml_file = "" then
			error "Giving up"  else ()
                val (thy_uptodate, ml_uptodate) =
                        thy_unchanged t thy_file ml_file;
             in if thy_uptodate andalso ml_uptodate then
 		(if !update_verbose then
 	         (writeln
 		   ("Not reading \"" ^ thy_file ^
 		          "\" (unchanged)" ^
 		    (if ml_file <> ""
 		      then "\nNot reading \"" ^ ml_file ^
 			   "\" (unchanged)"
 	              else "")))
 	         else ())
 		else use_thy t;
               reload_changed ts
            end
        | reload_changed [] = ();

     (*Remove all theories that are no descendants of ProtoPure.
       If there are still children in the deleted theory's list
       schedule them for reloading *)
     fun collect_garbage no_garbage =
       let fun collect ((tname, {children, ...}: thy_info) :: ts) =
                 if tname mem no_garbage then collect ts
                 else (writeln ("Theory \"" ^ tname ^
                       "\" is no longer linked with ProtoPure - removing it.");
                       remove_thy tname;
                       seq mark_outdated children)
             | collect [] = ()
       in collect (Symtab.dest (!loaded_thys)) end;
  in tmp_loadpath := [];
     collect_garbage ("ProtoPure" :: (load_order ["ProtoPure"] []));
     reload_changed (load_order ["Pure", "CPure"] [])
  end;


*)
