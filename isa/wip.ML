(* $Id *)
	
(* Work in progress for ProofGeneral.ML:  modified theory reader code. *)

	
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

