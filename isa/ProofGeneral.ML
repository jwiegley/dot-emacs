(* 
   Isabelle configuration for Proof General.

   Author:  David Aspinall <da@dcs.ed.ac.uk>
   Contact: Isabelle maintainer <isabelle@dcs.ed.ac.uk>

   $Id$

*)


val proof_state_special_prefix="\248";
val proof_state_special_suffix="\249";
val goal_start_special="\253";



(* val orig_prs_fn = !prs_fn; *)
(* val orig_warning_fn = !warning_fn; *)
(* val orig_error_fn = !error_fn; *)

(* copied from Pure/library.ML: *)
local
  fun out s =
    (TextIO.output (TextIO.stdOut, s); TextIO.flushOut TextIO.stdOut);

  fun prefix_lines prfx txt =
    txt |> split_lines |> map (fn s => prfx ^ s ^ "\n") |> implode;
in

(*hooks for output channels: normal, warning, error*)

(* Proof General: no change to these yet from defaults, but be
   careful that proof-shell-prompt-pattern doesn't match any
   of these!  (maybe the default needs adjustment)
*)
val () =
	(prs_fn := (fn s => out s);
	 warning_fn := (fn s => out (prefix_lines "### " s));
	 error_fn := (fn s => out (prefix_lines "*** " s)))

end;



local

  (* utils *)

  fun ins_entry (x, y) [] = [(x, [y])]
    | ins_entry (x, y) ((pair as (x', ys')) :: pairs) =
        if x = x' then (x', y ins ys') :: pairs
        else pair :: ins_entry (x, y) pairs;

  fun add_consts (Const (c, T), env) = ins_entry (T, (c, T)) env
    | add_consts (t $ u, env) = add_consts (u, add_consts (t, env))
    | add_consts (Abs (_, _, t), env) = add_consts (t, env)
    | add_consts (_, env) = env;

  fun add_vars (Free (x, T), env) = ins_entry (T, (x, ~1)) env
    | add_vars (Var (xi, T), env) = ins_entry (T, xi) env
    | add_vars (Abs (_, _, t), env) = add_vars (t, env)
    | add_vars (t $ u, env) = add_vars (u, add_vars (t, env))
    | add_vars (_, env) = env;

  fun add_varsT (Type (_, Ts), env) = foldr add_varsT (Ts, env)
    | add_varsT (TFree (x, S), env) = ins_entry (S, (x, ~1)) env
    | add_varsT (TVar (xi, S), env) = ins_entry (S, xi) env;

  fun sort_idxs vs = map (apsnd (sort (prod_ord string_ord int_ord))) vs;
  fun sort_cnsts cs = map (apsnd (sort_wrt fst)) cs;


  (* prepare atoms *)

  fun consts_of t = sort_cnsts (add_consts (t, []));
  fun vars_of t = sort_idxs (add_vars (t, []));
  fun varsT_of t = rev (sort_idxs (it_term_types add_varsT (t, [])));

in

  fun script_print_goals maxgoals state =
    let
      val {sign, ...} = rep_thm state;

      val prt_term = Sign.pretty_term sign;
      val prt_typ = Sign.pretty_typ sign;
      val prt_sort = Sign.pretty_sort sign;

      fun prt_atoms prt prtT (X, xs) = Pretty.block
        [Pretty.block (Pretty.commas (map prt xs)), Pretty.str " ::",
          Pretty.brk 1, prtT X];

      fun prt_var (x, ~1) = prt_term (Syntax.free x)
        | prt_var xi = prt_term (Syntax.var xi);

      fun prt_varT (x, ~1) = prt_typ (TFree (x, []))
        | prt_varT xi = prt_typ (TVar (xi, []));

      val prt_consts = prt_atoms (prt_term o Const) prt_typ;
      val prt_vars = prt_atoms prt_var prt_typ;
      val prt_varsT = prt_atoms prt_varT prt_sort;


      fun print_list _ _ [] = ()
        | print_list name prt lst = (writeln "";
            Pretty.writeln (Pretty.big_list name (map prt lst)));

      fun print_subgoals (_, []) = ()
        | print_subgoals (n, A :: As) = (Pretty.writeln (Pretty.blk (0,
            [Pretty.str (goal_start_special ^
			  " " ^ string_of_int n ^ ". "), prt_term A]));
              print_subgoals (n + 1, As));

      val print_ffpairs =
        print_list "Flex-flex pairs:" (prt_term o Logic.mk_flexpair);

      val print_consts = print_list "Constants:" prt_consts o consts_of;
      val print_vars = print_list "Variables:" prt_vars o vars_of;
      val print_varsT = print_list "Type variables:" prt_varsT o varsT_of;


      val {prop, ...} = rep_thm state;
      val (tpairs, As, B) = Logic.strip_horn prop;
      val ngoals = length As;

      fun print_gs (types, sorts) =
       (Pretty.writeln (prt_term B);
        if ngoals = 0 then writeln "No subgoals!"
        else if ngoals > maxgoals then
          (print_subgoals (1, take (maxgoals, As));
            writeln ("A total of " ^ string_of_int ngoals ^ " subgoals..."))
        else print_subgoals (1, As);

        print_ffpairs tpairs;

        if types andalso ! show_consts then print_consts prop else ();
        if types then print_vars prop else ();
        if sorts then print_varsT prop else ());
    in
      setmp show_no_free_types true
        (setmp show_types (! show_types orelse ! show_sorts)
          (setmp show_sorts false print_gs))
     (! show_types orelse ! show_sorts, ! show_sorts)
  end;

end;




(* Pure/goals.ML declares print_current_goals_fn. *)

val orig_print_current_goals_fn = !print_current_goals_fn;

fun script_mode_print_current_goals_fn n max th =
  (writeln ("Level " ^ string_of_int n); script_print_goals max th);

local
  fun out s =
    (TextIO.output (TextIO.stdOut, s); TextIO.flushOut TextIO.stdOut);
  fun cgf i j t =
     (out proof_state_special_prefix;
      script_mode_print_current_goals_fn i j t;
      out proof_state_special_suffix)
in
 val () = (print_current_goals_fn := cgf)
end



(* Some top-level commands for Proof General.
   These could easily be customized to do different things.
*)

structure ProofGeneral =
  struct
    fun kill_goal () = Goal "PROP no_goal_supplied";
    fun help () = print version;
    fun show_context () = the_context();
  end;       


(* duplicated code from thy_read.ML *)

val tmp_loadpath = ref [] : string list ref;

fun find_file "" name =
      let fun find_it (cur :: paths) =
                if File.exists (tack_on cur name) then
                  (if cur = "." then name else tack_on cur name)
                else
                  find_it paths
           | find_it [] = ""
      in find_it (!tmp_loadpath @ !loadpath) end
  | find_file path name =
      if File.exists (tack_on path name) then tack_on path name
                                         else "";

(*Get absolute pathnames for a new or already loaded theory *)
(*
fun get_filenames path name =
  let fun new_filename () =
        let val found = find_file path (name ^ ".thy");
            val absolute_path = absolute_path (OS.FileSys.getDir ());
            val thy_file = absolute_path found;
            val (thy_path, _) = split_filename thy_file;
            val found = find_file path (name ^ ".ML");
            val ml_file = if thy_file = "" then absolute_path found
                          else if File.exists (tack_on thy_path (name ^ ".ML"))
                          then tack_on thy_path (name ^ ".ML")
                          else "";
            val searched_dirs = if path = "" then (!tmp_loadpath @ !loadpath)
                                             else [path]
        in if thy_file = "" andalso ml_file = "" then
	     (* Proof General change: only give warning message here *)
             warning ("Could not find file \"" ^ name ^ ".thy\" or \""
                    ^ name ^ ".ML\" for theory \"" ^ name ^ "\"\n"
                    ^ "in the following directories: \"" ^
                    (space_implode "\", \"" searched_dirs) ^ "\"")
           else ();
           (thy_file, ml_file)
        end;

      val tinfo = get_thyinfo name;
  in if is_some tinfo andalso path = "" then
       let val {path = abs_path, ...} = the tinfo;
           val (thy_file, ml_file) = if abs_path = "" then new_filename ()
                                     else (find_file abs_path (name ^ ".thy"),
                                           find_file abs_path (name ^ ".ML"))
       in if thy_file = "" andalso ml_file = "" then
            (warning ("File \"" ^ (tack_on path name)
                      ^ ".thy\"\ncontaining theory \"" ^ name
                      ^ "\" no longer exists.");
             new_filename ()
            )
          else (thy_file, ml_file)
       end
     else new_filename ()
  end;
Not needed in latest version of Isabelle with my hack.
*)


fun retract_file thy =
  let fun file_msg x = if (x <> "") then
			writeln ("Proof General, you can unlock the file "
			     ^ (quote x))
	               else ()
      (* output messages for this theory *)
      val (thy_file, ml_file) = get_thy_filenames (path_of thy) thy
      val _ = file_msg thy_file
      val _ = file_msg ml_file
      (* now process this theory's children *)
      val children = children_of thy;
      val present = filter (is_some o get_thyinfo) children;
      fun already_loaded thy =
         let val t = get_thyinfo thy
      in if is_none t then false
         else let val {thy_time, ml_time, ...} = the t
      in is_some thy_time andalso is_some ml_time end
      end
      val loaded = filter already_loaded present;
   in      
      if loaded <> [] then
		(map retract_file loaded; ())
      else ()
   end;

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

(* Get Proof General to cache the loaded files. *)

list_loaded_files();
   


  

