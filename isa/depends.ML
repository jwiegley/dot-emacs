(* depends.ML

   Experimental code for communicating theorem dependencies from Isabelle
   to Proof General.

   This code is taken from thm_deps.ML in Isabelle 99-2.  It's incompatible
   with other Isabelle versions.

   It is duplicated almost verbatim because what we need is
   hardwired to a call on the browser tool.
*)


fun depends_enable () = Thm.keep_derivs := ThmDeriv;
fun depends_disable () = Thm.keep_derivs := MinDeriv;



fun is_internal (name, tags) = name = "" orelse Drule.has_internal tags;

fun is_thm_axm (Theorem x) = not (is_internal x)
  | is_thm_axm (Axiom x) = not (is_internal x)
  | is_thm_axm _ = false;

fun get_name (Theorem (s, _)) = s
  | get_name (Axiom (s, _)) = s
  | get_name _ = "";

fun make_deps_graph ((gra, parents), Join (ta, ders)) =
  let
    val name = get_name ta;
  in
    if is_thm_axm ta then
      if is_none (Symtab.lookup (gra, name)) then
        let
          val (gra', parents') = foldl make_deps_graph ((gra, []), ders);
          val prefx = #1 (Library.split_last (NameSpace.unpack name));
          val session =
            (case prefx of
              (x :: _) =>
                (case ThyInfo.lookup_theory x of
                  Some thy =>
                    let val name = #name (Present.get_info thy)
                    in if name = "" then [] else [name] end 
                | None => [])
             | _ => ["global"]);
        in
          (Symtab.update ((name,
            {name = Sign.base_name name, ID = name,
             dir = space_implode "/" (session @ prefx),
             unfold = false, path = "", parents = parents'}), gra'), name ins parents)
        end
      else (gra, name ins parents)
    else
      foldl make_deps_graph ((gra, parents), ders)
  end;

fun thm_deps thms =
  let
    val _ = writeln "Generating graph ...";
    val gra = map snd (Symtab.dest (fst (foldl make_deps_graph ((Symtab.empty, []),
      map (#2 o #der o Thm.rep_thm) thms))));
    val path = File.tmp_path (Path.unpack "theorems.graph");
    val _ = Present.write_graph gra path;
    val _ = system ("$ISATOOL browser -d " ^ Path.pack (Path.expand path) ^ " &");
  in () end;

fun new_thm_deps thms =
  let
    val header = "Proof General, the theorem dependencies are: \"";
    val gra = map snd (Symtab.dest (fst (foldl make_deps_graph ((Symtab.empty, []),
      map (#2 o #der o Thm.rep_thm) thms))));
    val deps = foldl (op@) ([],(map #parents gra))
    val msg = header ^ (space_implode " " deps) ^ "\""
  in priority msg end;

val old_qed = qed;

fun qed s = 
  let val _ = old_qed s
      val proved_thm = thm s
   in new_thm_deps [proved_thm] end;


