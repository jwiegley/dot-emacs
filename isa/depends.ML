
fun enable () = Thm.keep_derivs := ThmDeriv;
fun disable () = Thm.keep_derivs := MinDeriv;

enable();

fun get_sess thy = if Theory.eq_thy (thy, ProtoPure.thy) then ["Pure"]
  else
    (case #session (Present.get_info thy) of
        [x] => [x, "base"]
      | xs => xs);

fun put_graph gr path =
    File.write path (cat_lines (map (fn {name, ID, dir, unfold, path, parents} =>
      "\"" ^ name ^ "\" \"" ^ ID ^ "\" \"" ^ dir ^ (if unfold then "\" + \"" else "\" \"") ^
      path ^ "\" > " ^ space_implode " " (map quote parents) ^ " ;") gr));

fun is_thm_axm (Theorem _) = true
  | is_thm_axm (Axiom _) = true
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
          val prefx = rev (tl (rev (NameSpace.unpack name)));
          val session = (case prefx of
               (x :: _) => (case ThyInfo.lookup_theory x of
                     (Some thy) => get_sess thy
                   | None => [])
             | _ => ["global"])
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
      map (#der o rep_thm) thms))));
    val path = File.tmp_path (Path.unpack "theorems.graph");
    val _ = put_graph gra path;
    val _ = system ("$ISATOOL browser -d " ^ Path.pack (Path.expand path) ^ " &");
  in () end;

fun new_thm_deps thms =
  let
    val _ = print "Proof General, the theorem dependencies are:   ";
    val gra = map snd (Symtab.dest (fst (foldl make_deps_graph ((Symtab.empty, []),
      map (#der o rep_thm) thms))));
    fun printname s = (print s; print " ");
    val _ = seq printname (foldl (op@) ([],(map #parents gra)));
  in writeln "" end;

val old_qed = qed;

fun qed s = 
  let val _ = old_qed s
      val proved_thm = thm s
   in new_thm_deps [proved_thm] end;


